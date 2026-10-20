import R17MinimalReverseBits
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace R17TableAChunk04Certificate
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

theorem power_128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 128 = ⟨212706801, 1223819887⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_64]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_129 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 129 = ⟨635733977, 1147342686⟩ := by
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

theorem power_137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 137 = ⟨1581084279, 1857932412⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 144 = ⟨552528648, 1672522617⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_145 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 145 = ⟨1560614480, 360987849⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_72]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_146 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 146 = ⟨1394961978, 1918912426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73]
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

theorem power_178 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 178 = ⟨1966870087, 1210006847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_89]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185 = ⟨1288520283, 160642759⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193 = ⟨631469289, 1565061397⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96]
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

theorem power_201 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 201 = ⟨1520147888, 325985670⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_209 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 209 = ⟨1797275270, 153051719⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210 = ⟨1496414007, 1479063729⟩ := by
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

theorem power_242 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 242 = ⟨1632899039, 338964697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_121]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_249 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 249 = ⟨1744129065, 1490136674⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_124]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 256 = ⟨421007138, 256177860⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_258 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 258 = ⟨262969597, 504539214⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_129]
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

theorem power_274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 274 = ⟨2072356374, 911719338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 288 = ⟨1178716014, 1579375203⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_290 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 290 = ⟨156662592, 909666249⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_145]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_292 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 292 = ⟨1014560274, 418534048⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_146]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 306 = ⟨1302783265, 1840133980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_322 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 322 = ⟨1778301183, 2036177926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_161]
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

theorem power_338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 338 = ⟨1774142499, 1307308901⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354 = ⟨1847155883, 1096249344⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_356 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 356 = ⟨115833841, 1001104970⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_178]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_370 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 370 = ⟨437004439, 622531583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_386 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 386 = ⟨1985386694, 853298120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193]
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

theorem power_402 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 402 = ⟨684316640, 356521895⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_201]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_418 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 418 = ⟨484064663, 997873469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_209]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_420 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 420 = ⟨762451310, 2110959177⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_434 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 434 = ⟨945282890, 1431558057⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_217]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 450 = ⟨724983407, 589107293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_225]
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

theorem power_466 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466 = ⟨1124251816, 63530739⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 482 = ⟨604694560, 1964390835⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_484 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 484 = ⟨1722484487, 1875389337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_242]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_498 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 498 = ⟨1596061297, 646835308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_249]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 512 = ⟨6346213, 905523693⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_516 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 516 = ⟨782339391, 1827324837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_258]
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

theorem power_548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 548 = ⟨866115909, 1643827515⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 576 = ⟨1603309155, 1317339952⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_580 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 580 = ⟨369747845, 887373134⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_290]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 584 = ⟨1408296071, 1181839931⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_292]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 612 = ⟨2046256912, 509115615⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_644 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 644 = ⟨1257431253, 699273795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_322]
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

theorem power_676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 676 = ⟨393415872, 860368912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708 = ⟨457829643, 1941425476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 712 = ⟨1788714561, 1660296709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_356]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_740 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 740 = ⟨197719403, 1999852429⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_370]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_772 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 772 = ⟨1798781646, 1865266823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_386]
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

theorem power_804 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 804 = ⟨26399338, 967637504⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_402]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_836 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 836 = ⟨83655737, 2124043286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_418]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 840 = ⟨667660294, 1845636271⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_420]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_868 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 868 = ⟨2142650926, 908959764⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_434]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 900 = ⟨612410710, 136959994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_450]
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

theorem power_932 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 932 = ⟨1976405820, 1310158830⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 964 = ⟨2118143742, 705646937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 968 = ⟨331985874, 1829534965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_484]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_996 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 996 = ⟨908566887, 550594540⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_498]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1024 = ⟨1022251061, 788094511⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1032 = ⟨1481817559, 1744156873⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_516]
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

theorem power_1096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1096 = ⟨1501894557, 1834033800⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1152 = ⟨2144756169, 1973977555⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1160 = ⟨1896703716, 628956045⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_580]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1168 = ⟨341432789, 740546388⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1224 = ⟨1026227221, 2108794965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1288 = ⟨1343759381, 1864045884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_644]
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

theorem power_1352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1352 = ⟨1927061498, 1374927155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1416 = ⟨1193898582, 1576714415⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_708]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1424 = ⟨1421359463, 688309433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1480 = ⟨722960591, 588699063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_740]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1544 = ⟨1068029906, 646532063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_772]
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

theorem power_1608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1608 = ⟨62787373, 919735329⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_804]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1672 = ⟨694287611, 660331636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_836]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1680 = ⟨97994513, 427567333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1736 = ⟨467721784, 1602005661⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_868]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1800 = ⟨1986113118, 992825915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_900]
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

theorem power_1864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1864 = ⟨1968067598, 686949896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_932]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1928 = ⟨936181679, 1735398398⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1936 = ⟨440725243, 397214378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1992 = ⟨1008494537, 585464310⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_996]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2048 = ⟨1633461177, 574296567⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2064 = ⟨1860848169, 298938599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1032]
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

theorem power_2192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2192 = ⟨1742105348, 871429063⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2304 = ⟨505774551, 1187398701⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2320 = ⟨280513604, 22556028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2336 = ⟨1969372346, 488760614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2448 = ⟨481345752, 412268047⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2576 = ⟨910702273, 1588993839⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1288]
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

theorem power_2704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2704 = ⟨1366684352, 516929062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2832 = ⟨1549367885, 715283423⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2848 = ⟨1107539930, 1867229522⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2960 = ⟨2097605752, 220649565⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3088 = ⟨1786181340, 1404427494⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1544]
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

theorem power_3216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3216 = ⟨731685287, 762627775⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3344 = ⟨1194090073, 1501677440⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3360 = ⟨957961597, 1713758465⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3472 = ⟨1911499284, 1489701003⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3600 = ⟨1593351449, 859601116⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1800]
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

theorem power_3728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3728 = ⟨390407353, 375027877⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3856 = ⟨288562008, 235863280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3872 = ⟨732405916, 440343212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3984 = ⟨1686898389, 320083871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4097 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4097 = ⟨1201423577, 1817022349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4128 = ⟨152579518, 1401481845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2064]
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

theorem power_4384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4384 = ⟨1196533489, 306824470⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4608 = ⟨1781794005, 336873408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4640 = ⟨1968119031, 1953739867⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4672 = ⟨2028679962, 456227245⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4896 = ⟨23461219, 810403446⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5152 = ⟨915810530, 1384603928⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2576]
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

theorem power_5408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5408 = ⟨2064549844, 501529631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5664 = ⟨1026601736, 1271844727⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5696 = ⟨979531440, 1806178696⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5920 = ⟨878312693, 56859138⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6176 = ⟨315754747, 208044896⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3088]
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

theorem power_6432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6432 = ⟨619638383, 840515631⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6688 = ⟨769754617, 38321535⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6720 = ⟨618506335, 666669213⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6944 = ⟨1264135541, 1176714595⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7200 = ⟨1184721950, 878005396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3600]
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

theorem power_7456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7456 = ⟨645077113, 2009296946⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7712 = ⟨882289621, 2131737122⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7744 = ⟨1314764028, 76457491⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7968 = ⟨1615077929, 1550574971⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8194 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8194 = ⟨35141171, 1925628378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4097]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8256 = ⟨1893959686, 1568143280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4128]
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

theorem power_8768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8768 = ⟨1312321620, 449496866⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9216 = ⟨1702571195, 1397706324⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9280 = ⟨712478805, 1515677912⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9344 = ⟨1549016389, 59136170⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9792 = ⟨1641904899, 479652953⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10304 = ⟨1028494420, 870500944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5152]
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

theorem power_10816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10816 = ⟨589196420, 1478404190⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11328 = ⟨451500757, 1042820697⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11392 = ⟨1624277146, 218264369⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11840 = ⟨1936539270, 2080532700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12352 = ⟨365044361, 1180771663⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6176]
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

theorem power_12864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12864 = ⟨1849520254, 294275432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13376 = ⟨1082234746, 1195886797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13440 = ⟨1254228892, 1773606283⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13888 = ⟨999173566, 53735745⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14400 = ⟨852788928, 1407244314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7200]
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

theorem power_14912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14912 = ⟨1832078956, 1219025627⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15424 = ⟨1562032226, 1259672017⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15488 = ⟨2114691705, 1438921723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15936 = ⟨1702528037, 2011195799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16388 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16388 = ⟨35956957, 1503319718⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8194]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16512 = ⟨1291076935, 1070127583⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8256]
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

theorem power_17536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17536 = ⟨1806498481, 2062496117⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18432 = ⟨1139757936, 161139962⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18560 = ⟨1694057790, 1757463169⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18688 = ⟨645114853, 992481545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19584 = ⟨1580867433, 1644740200⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20608 = ⟨1806350313, 1284788848⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10304]
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

theorem power_21632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21632 = ⟨2099551557, 403675340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22656 = ⟨54122264, 999860590⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22784 = ⟨136897115, 493987288⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23680 = ⟨854568819, 1347442685⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24704 = ⟨872353324, 999049023⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12352]
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

theorem power_25728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25728 = ⟨1759013300, 1042401069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26752 = ⟨1177452963, 1170167703⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26880 = ⟨676135582, 533441857⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27776 = ⟨1834226232, 553776749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28800 = ⟨305787977, 153981243⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14400]
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

theorem power_29824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29824 = ⟨1483663201, 1628565788⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30848 = ⟨1625013772, 728500935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30976 = ⟨1799654460, 431926545⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31872 = ⟨1943795279, 465690519⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32776 = ⟨1126694174, 1757455573⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16388]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33024 = ⟨1891007546, 749012277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16512]
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

theorem power_35072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35072 = ⟨1205114505, 1030165210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_36865 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 36865 = ⟨1735813234, 1752853531⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37120 = ⟨167491913, 1919872944⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37376 = ⟨1433248480, 2047948056⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_39168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 39168 = ⟨1100489519, 1086275843⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_41216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 41216 = ⟨1279689336, 292450238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20608]
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

theorem power_43264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 43264 = ⟨1891533946, 2050936908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45312 = ⟨452740335, 590580947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_45568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 45568 = ⟨1781787493, 1860062069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_47360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 47360 = ⟨578477849, 1590460480⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_49408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 49408 = ⟨857744938, 166099594⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24704]
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

theorem power_51456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51456 = ⟨1116504179, 647757200⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53504 = ⟨1164523761, 45068006⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_53760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 53760 = ⟨2139509494, 188640990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55552 = ⟨114992383, 2037241690⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_57600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 57600 = ⟨1886078852, 330853404⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28800]
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

theorem power_59648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59648 = ⟨724181499, 1793728645⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61696 = ⟨2110901694, 1683066232⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61952 = ⟨489478772, 1893340241⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63744 = ⟨1980320235, 603453234⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65552 = ⟨1632137722, 2009383978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_66048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 66048 = ⟨67188071, 768461072⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33024]
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

theorem power_69633 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69633 = ⟨1562101720, 2048038926⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_70144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 70144 = ⟨595073736, 1818489881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_73730 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 73730 = ⟨111911113, 279480897⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_36865]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74240 = ⟨2081413072, 246071924⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_74752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 74752 = ⟨650673267, 783237242⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_37376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_78336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 78336 = ⟨411448928, 233625844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_39168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_82432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 82432 = ⟨321123339, 28578597⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_41216]
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

theorem power_86528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 86528 = ⟨434707223, 1389804667⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_43264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_90624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 90624 = ⟨898664610, 1196473364⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_91136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 91136 = ⟨1033720207, 1183348280⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_45568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_94720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 94720 = ⟨655661521, 997404908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_47360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_98816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 98816 = ⟨1094208192, 1382666258⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_49408]
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

theorem power_102401 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102401 = ⟨1095546490, 1163658850⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102912 = ⟨1504273585, 1801154452⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107008 = ⟨603993480, 1658961978⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_107520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 107520 = ⟨250559477, 97699828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_53760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_111104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 111104 = ⟨1107514854, 789018799⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_115200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 115200 = ⟨2115839553, 607309935⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_57600]
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

theorem power_119296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119296 = ⟨383390103, 624803601⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123392 = ⟨981855613, 2026394432⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_123904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 123904 = ⟨1105219207, 965100990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_127488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 127488 = ⟨829291870, 806666746⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_131104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 131104 = ⟨446512071, 53084673⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_132096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 132096 = ⟨1545848211, 634791136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_133120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 133120 = ⟨1343125376, 1611076075⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_66560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135169 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135169 = ⟨1209541918, 1008279614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_139266 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 139266 = ⟨1855444314, 1481792923⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69633]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_140288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 140288 = ⟨809678638, 323259731⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_70144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_147460 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 147460 = ⟨1001764359, 369939251⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_73730]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_148480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 148480 = ⟨1897626162, 1847676603⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_149504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 149504 = ⟨1071628068, 1255434837⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_74752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_156672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 156672 = ⟨2038368826, 1106226198⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_78336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_164864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 164864 = ⟨285695498, 613980118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_165888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 165888 = ⟨821570021, 1145420705⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_82944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_167937 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 167937 = ⟨1024914866, 457984155⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_83968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_173056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 173056 = ⟨737486420, 1841785488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_86528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_181248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 181248 = ⟨1395504571, 607335160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_90624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_182272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 182272 = ⟨1309999598, 467334114⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_91136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_189440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 189440 = ⟨1040456537, 1941786120⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_94720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_197632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 197632 = ⟨1444784472, 1256093482⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_98816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_198656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 198656 = ⟨1408282706, 600722738⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_99328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_200705 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 200705 = ⟨2098937916, 898508269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_100352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_204802 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 204802 = ⟨1604555490, 1237190381⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102401]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205824 = ⟨1412850982, 862664749⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_214016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 214016 = ⟨715353272, 286494838⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_215040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 215040 = ⟨511564144, 1485902172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_107520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_222208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 222208 = ⟨881063582, 942487649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_111104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_230400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 230400 = ⟨1365609705, 1009341282⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_231424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 231424 = ⟨1423034495, 1044300741⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_115712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_233473 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 233473 = ⟨1816900591, 605475336⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_116736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_238592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 238592 = ⟨1558946112, 74958411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_246784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 246784 = ⟨1038693574, 1287133297⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_247808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 247808 = ⟨1752942601, 1104368066⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_123904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_254976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 254976 = ⟨399181318, 1588403662⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_127488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_262208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 262208 = ⟨589818940, 1925605983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_131104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_264192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 264192 = ⟨302125271, 1416107052⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_132096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_266241 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 266241 = ⟨605306994, 1789899750⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_133120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270338 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270338 = ⟨121224103, 143158037⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135169]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_278532 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 278532 = ⟨856759523, 1663490210⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_139266]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_280576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 280576 = ⟨301592792, 2080568233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_140288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_294920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 294920 = ⟨2052912105, 766541433⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_147460]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_296960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 296960 = ⟨295990997, 941692002⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_148480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_299009 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 299009 = ⟨1180980793, 109645561⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_149504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_313344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 313344 = ⟨1519289632, 554415477⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_156672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_329728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 329728 = ⟨985045909, 786285443⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_164864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_331777 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 331777 = ⟨367360429, 1262961956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_165888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_335874 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 335874 = ⟨790375455, 1807754692⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_167937]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_346112 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 346112 = ⟨1396387241, 1636248379⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_173056]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_362496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 362496 = ⟨966434100, 857433908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_181248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_364545 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 364545 = ⟨835793988, 1276450497⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_182272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_378880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 378880 = ⟨796901153, 679264882⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_189440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_395264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 395264 = ⟨1338663259, 1317602281⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_197632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_397313 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 397313 = ⟨1384338533, 1607277425⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_198656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_401410 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 401410 = ⟨1578801829, 138852068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_200705]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_409604 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 409604 = ⟨1192254760, 426449396⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_204802]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_411648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 411648 = ⟨1993145094, 1556913362⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_205824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_428032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 428032 = ⟨492808319, 1202170691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_214016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_430081 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 430081 = ⟨886324786, 751911710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_215040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_444416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 444416 = ⟨833065953, 160077459⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_222208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_460800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 460800 = ⟨1180239345, 1380236185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_230400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_462849 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 462849 = ⟨1077046543, 675423367⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_231424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_466946 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 466946 = ⟨1615072020, 1511296402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_233473]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_477184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 477184 = ⟨1762390813, 1601969049⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_238592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_493568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 493568 = ⟨712896677, 412924820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_246784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_495617 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 495617 = ⟨912699495, 1050298589⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_247808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_509952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 509952 = ⟨1277755557, 2036963937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_254976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_524416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 524416 = ⟨199040872, 1126113092⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_262208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_528385 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 528385 = ⟨845903248, 1607632176⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_264192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_532482 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 532482 = ⟨2020160623, 1719914591⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_266241]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_540676 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 540676 = ⟨2024252161, 1153237408⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270338]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_557064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 557064 = ⟨1066413358, 1994987263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_278532]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_561153 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 561153 = ⟨522620114, 1299964410⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_280576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_589840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 589840 = ⟨27999500, 1303558959⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_294920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_593921 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 593921 = ⟨874766058, 1801863732⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_296960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_598018 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 598018 = ⟨412142412, 1691360823⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_299009]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_626689 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 626689 = ⟨466920358, 1153653050⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_313344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_659457 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 659457 = ⟨347127345, 1239982270⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_329728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_663554 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 663554 = ⟨506186870, 1373161337⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_331777]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_671748 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 671748 = ⟨1131594933, 800395149⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_335874]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_692225 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 692225 = ⟨1362139903, 1360887520⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_346112]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_724993 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 724993 = ⟨1010091500, 1594888058⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_362496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_729090 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 729090 = ⟨2049861632, 1087198964⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_364545]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_757761 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 757761 = ⟨845462111, 1309183427⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_378880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_790529 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 790529 = ⟨2002375625, 342419305⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_395264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_794626 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 794626 = ⟨1220703602, 654520444⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_397313]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_802820 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 802820 = ⟨1882983941, 1638752064⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_401410]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_819208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 819208 = ⟨1018462047, 1963766992⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_409604]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_823297 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 823297 = ⟨173885738, 1193716652⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_411648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_856065 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 856065 = ⟨1745905207, 2031279512⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_428032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_860162 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 860162 = ⟨1869883508, 1559193340⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_430081]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_888833 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 888833 = ⟨1624662861, 1425887039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_444416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_921601 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 921601 = ⟨284994215, 443285672⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_460800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_925698 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 925698 = ⟨1359515546, 2012813983⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_462849]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_933892 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 933892 = ⟨1459739827, 342836378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_466946]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_954369 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 954369 = ⟨1684462187, 1864157028⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_477184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_987137 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 987137 = ⟨38873044, 615411602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_493568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_991234 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 991234 = ⟨763461971, 94970306⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_495617]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1019905 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1019905 = ⟨1213990669, 1695366296⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_509952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1048832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1048832 = ⟨1560785735, 1924473095⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_524416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1056770 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1056770 = ⟨544374302, 472977929⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_528385]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1064964 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1064964 = ⟨505528787, 834860372⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_532482]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1081352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1081352 = ⟨1772545630, 1507996303⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_540676]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1114128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1114128 = ⟨1049855557, 80952493⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_557064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1122306 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1122306 = ⟨2126915626, 1716968360⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_561153]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1179680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1179680 = ⟨1765315889, 1724293373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_589840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1187842 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1187842 = ⟨916961822, 1132101338⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_593921]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1196036 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1196036 = ⟨928062765, 1611614844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_598018]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1253378 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1253378 = ⟨2066992088, 317617096⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_626689]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1318914 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1318914 = ⟨2013915575, 1724669524⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_659457]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1327108 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1327108 = ⟨68794991, 1996250156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_663554]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1343496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1343496 = ⟨1405643163, 263388879⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_671748]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1384450 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1384450 = ⟨502186305, 1347367269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_692225]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1449986 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1449986 = ⟨2053980605, 1349238395⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_724993]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1458180 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1458180 = ⟨2109804070, 571255462⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_729090]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1515522 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1515522 = ⟨595222590, 35787285⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_757761]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1581058 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1581058 = ⟨2088792393, 625224853⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_790529]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1589252 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1589252 = ⟨697505, 292726334⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_794626]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1605640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1605640 = ⟨722174366, 410765088⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_802820]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1638416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1638416 = ⟨58930785, 777689235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_819208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1646594 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1646594 = ⟨210216093, 487992523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_823297]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1712130 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1712130 = ⟨1754599432, 109970814⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_856065]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1720324 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1720324 = ⟨1361094725, 123467687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_860162]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1777666 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1777666 = ⟨1762083425, 1234767780⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_888833]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1843202 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1843202 = ⟨429305014, 998984464⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_921601]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1851396 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1851396 = ⟨1660190186, 55114579⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_925698]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1867784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1867784 = ⟨966613606, 578713810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_933892]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1908738 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1908738 = ⟨1556013387, 396658231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_954369]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1974274 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1974274 = ⟨348784773, 1251949797⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_987137]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1982468 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1982468 = ⟨709928380, 1564198880⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_991234]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2039810 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2039810 = ⟨350421379, 2083039684⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1019905]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2097664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2097664 = ⟨1243028821, 2009537794⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1048832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2113540 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2113540 = ⟨841376247, 1200623126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1056770]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2129928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2129928 = ⟨209411925, 73314994⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1064964]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2162704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2162704 = ⟨148073515, 1758172723⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1081352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2228256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2228256 = ⟨142853477, 1019843416⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1114128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2244612 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2244612 = ⟨2041114998, 733769861⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1122306]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2359360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2359360 = ⟨1237451345, 823713884⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1179680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2375684 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2375684 = ⟨865335467, 51820031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1187842]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2392072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2392072 = ⟨1332364484, 2042571455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1196036]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2506756 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2506756 = ⟨1105972722, 337914453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1253378]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2637828 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2637828 = ⟨161378202, 513466650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1318914]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2654216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2654216 = ⟨1395276262, 1291811098⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1327108]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2686992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2686992 = ⟨1294945584, 1237559394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1343496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2768900 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2768900 = ⟨1333657299, 269277868⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1384450]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2899972 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2899972 = ⟨1238913079, 6710485⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1449986]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_2916360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 2916360 = ⟨1530970342, 731923534⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1458180]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3031044 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3031044 = ⟨976740682, 289617975⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1515522]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3162116 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3162116 = ⟨1484113507, 633067435⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1581058]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3178504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3178504 = ⟨216357958, 1410298055⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1589252]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3211280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3211280 = ⟨257733445, 1689230373⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1605640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3276832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3276832 = ⟨1909947292, 1946348383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1638416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3293188 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3293188 = ⟨22220232, 1650644730⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1646594]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3424260 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3424260 = ⟨2139606984, 2029135125⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1712130]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3440648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3440648 = ⟨982253514, 1303566026⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1720324]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3555332 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3555332 = ⟨895755299, 231596293⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1777666]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3686404 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3686404 = ⟨1440038000, 91935546⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1843202]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3702792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3702792 = ⟨1895635813, 1848037191⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1851396]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3735568 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3735568 = ⟨233671981, 1046307308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1867784]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3817476 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3817476 = ⟨966318326, 1916425937⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1908738]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3948548 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3948548 = ⟨2065296713, 1994713472⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1974274]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_3964936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 3964936 = ⟨2106721093, 689506389⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_1982468]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4079620 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4079620 = ⟨1400477745, 1024351950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2039810]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4195328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4195328 = ⟨789199007, 265368403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2097664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4227080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4227080 = ⟨351160504, 1094930568⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2113540]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4259856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4259856 = ⟨1892390403, 392754231⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2129928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4325408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4325408 = ⟨1516516329, 1369776185⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2162704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4456512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4456512 = ⟨1548170328, 133828081⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2228256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4489224 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4489224 = ⟨478368710, 1497750785⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2244612]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4718720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4718720 = ⟨1049861288, 826580816⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2359360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4751368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4751368 = ⟨2037165791, 1078751195⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2375684]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_4784144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 4784144 = ⟨1545369175, 1521290411⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2392072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5013512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5013512 = ⟨198791338, 1996036941⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2506756]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5275656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5275656 = ⟨250603746, 1446832809⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2637828]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5308432 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5308432 = ⟨1295128400, 462507286⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2654216]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5373984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5373984 = ⟨2061616816, 2107376636⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2686992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5537800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5537800 = ⟨103205110, 1057308279⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2768900]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5799944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5799944 = ⟨2098801084, 1290442909⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2899972]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_5832720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 5832720 = ⟨315622234, 597934345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_2916360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6062088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6062088 = ⟨1830013927, 1191390022⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3031044]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6324232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6324232 = ⟨2059095773, 660278059⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3162116]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6357008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6357008 = ⟨261488346, 242670187⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3178504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6422560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6422560 = ⟨1576213374, 63498499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3211280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6553664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6553664 = ⟨1911443490, 933881660⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3276832]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6586376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6586376 = ⟨14867637, 543851354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3293188]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6848520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6848520 = ⟨2034907477, 1970868182⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3424260]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_6881296 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 6881296 = ⟨1332676772, 1955687523⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3440648]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7110664 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7110664 = ⟨695087644, 385943345⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3555332]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7372808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7372808 = ⟨1952878847, 1750689084⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3686404]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7405584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7405584 = ⟨1486533776, 791024469⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3702792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7471136 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7471136 = ⟨224470758, 524081212⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3735568]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7634952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7634952 = ⟨64342087, 194792649⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3817476]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7897096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7897096 = ⟨556544052, 647251454⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3948548]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_7929872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 7929872 = ⟨803015447, 289874765⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_3964936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8159240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8159240 = ⟨1786297477, 1920175659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4079620]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8454160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8454160 = ⟨476605727, 1078479141⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4227080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8519712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8519712 = ⟨136191162, 589451376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4259856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8650816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8650816 = ⟨1489486595, 490956622⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4325408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8913024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8913024 = ⟨739557941, 281137576⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4456512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_8978448 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 8978448 = ⟨1557131535, 1949058071⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4489224]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9437440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9437440 = ⟨248098938, 843494796⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4718720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9502736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9502736 = ⟨160922190, 1308510129⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4751368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_9568288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 9568288 = ⟨1208648708, 1496667600⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_4784144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10027024 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10027024 = ⟨1835988840, 813247881⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5013512]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10551312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10551312 = ⟨1193887804, 1687108354⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5275656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10616864 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10616864 = ⟨1474011468, 1350731277⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5308432]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_10747968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 10747968 = ⟨588862459, 785633420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5373984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11075600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11075600 = ⟨506066422, 1964026766⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5537800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11599888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11599888 = ⟨2140264715, 1416945783⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5799944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_11665440 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 11665440 = ⟨975052095, 1657001135⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_5832720]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12124176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12124176 = ⟨1934346636, 801405239⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6062088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12648464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12648464 = ⟨1370429038, 105527308⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6324232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12714016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12714016 = ⟨1790857799, 1240208314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6357008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_12845120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 12845120 = ⟨171558755, 707548161⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6422560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13107328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13107328 = ⟨57379685, 1213083068⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6553664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13172752 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13172752 = ⟨1538937882, 1404785965⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6586376]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13697040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13697040 = ⟨2110974800, 1036709700⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6848520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_13762592 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 13762592 = ⟨1335635990, 429968536⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_6881296]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14221328 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14221328 = ⟨1049613327, 1577646874⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7110664]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14745616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14745616 = ⟨1046228478, 1033138152⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7372808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14811168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14811168 = ⟨1944094850, 160406233⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7405584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_14942272 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 14942272 = ⟨993409166, 763765488⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7471136]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15269904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15269904 = ⟨434428995, 634962844⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7634952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15794192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15794192 = ⟨387499351, 1707787845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7897096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_15859744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 15859744 = ⟨1412275163, 2108612710⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_7929872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16318480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16318480 = ⟨136842864, 1201155570⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8159240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_16908320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 16908320 = ⟨1275256159, 1113832455⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8454160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17039424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17039424 = ⟨1051329440, 1848259752⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8519712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17301632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17301632 = ⟨563538909, 1121010847⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8650816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17826048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17826048 = ⟨1704284085, 1070472990⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8913024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_17956896 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 17956896 = ⟨152499820, 1125015378⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_8978448]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_18874880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 18874880 = ⟨1709354262, 377188827⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9437440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19005472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19005472 = ⟨2119491698, 1942404845⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9502736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_19136576 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 19136576 = ⟨2044717794, 1658050403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_9568288]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_20054048 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 20054048 = ⟨1947365280, 1458686598⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10027024]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21102624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21102624 = ⟨1314082565, 650677160⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10551312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21233728 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21233728 = ⟨65891676, 417311101⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10616864]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_21495936 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 21495936 = ⟨1550134801, 1234966724⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_10747968]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_22151200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 22151200 = ⟨1215365856, 1460670950⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11075600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23199776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23199776 = ⟨2134601396, 1740336350⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11599888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_23330880 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 23330880 = ⟨150818351, 2034648526⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_11665440]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_24248352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 24248352 = ⟨1293877038, 193236131⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12124176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25296928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25296928 = ⟨2029469260, 1775853156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12648464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25428032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25428032 = ⟨1102300646, 150531516⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12714016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_25690240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 25690240 = ⟨1147429641, 202475204⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_12845120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26214656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26214656 = ⟨1624798585, 442460333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13107328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_26345504 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 26345504 = ⟨508175083, 760805560⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13172752]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27394080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27394080 = ⟨108433485, 522740453⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13697040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_27525184 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 27525184 = ⟨1387763624, 2105356767⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_13762592]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_28442656 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 28442656 = ⟨1979555800, 1609073650⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14221328]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29491232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29491232 = ⟨2053746151, 1822826090⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14745616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29622336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29622336 = ⟨1113768536, 1299147172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14811168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_29884544 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 29884544 = ⟨1872036796, 930479069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_14942272]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_30539808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 30539808 = ⟨1613787529, 1423607434⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15269904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31588384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31588384 = ⟨2100551309, 2091203087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15794192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_31719488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 31719488 = ⟨846836817, 1176144402⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_15859744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_32636960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 32636960 = ⟨145424045, 1324253377⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16318480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_33816640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 33816640 = ⟨337191012, 1604258619⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_16908320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34078848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34078848 = ⟨1584755368, 1828408156⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17039424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_34603264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 34603264 = ⟨104333490, 481418400⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17301632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35652096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35652096 = ⟨138611677, 987670751⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17826048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_35913792 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 35913792 = ⟨1087502506, 1659902392⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_17956896]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_37749760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 37749760 = ⟨2045776109, 764411913⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_18874880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38010944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38010944 = ⟨143526362, 1731304920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19005472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_38273152 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 38273152 = ⟨1251057307, 1416990426⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_19136576]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_40108096 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 40108096 = ⟨417014260, 1684317753⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_20054048]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42205248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42205248 = ⟨589277503, 1752042172⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21102624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42467456 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42467456 = ⟨643605806, 403637898⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21233728]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_42991872 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 42991872 = ⟨952876712, 881753333⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_21495936]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_44302400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 44302400 = ⟨1703908869, 738114284⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_22151200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46399552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46399552 = ⟨446591916, 833364080⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23199776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_46661760 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 46661760 = ⟨584095579, 1150021712⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_23330880]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_48496704 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 48496704 = ⟨1329069457, 1172591062⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_24248352]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50593856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50593856 = ⟨1883550178, 1339094605⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25296928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_50856064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 50856064 = ⟨213039164, 860654394⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25428032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_51380480 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 51380480 = ⟨1673911434, 1568448263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_25690240]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52429312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52429312 = ⟨1992024806, 800548087⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26214656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_52691008 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 52691008 = ⟨529817102, 1665121795⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_26345504]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_54788160 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 54788160 = ⟨1766622468, 399417278⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27394080]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_55050368 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 55050368 = ⟨49790919, 807987694⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_27525184]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_56885312 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 56885312 = ⟨1661159939, 1567254602⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_28442656]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_58982464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 58982464 = ⟨2103681635, 1672100106⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29491232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59244672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59244672 = ⟨1118782906, 1519883119⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29622336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_59769088 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 59769088 = ⟨72754186, 1864686934⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_29884544]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_61079616 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 61079616 = ⟨470151144, 804378608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_30539808]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63176768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63176768 = ⟨876378803, 444969735⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31588384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_63438976 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 63438976 = ⟨1459033199, 1933753074⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_31719488]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_65273920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 65273920 = ⟨392956505, 282965136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_32636960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_67633280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 67633280 = ⟨1972505658, 2124203039⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_33816640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_68157696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 68157696 = ⟨1295906005, 1809968659⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34078848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_69206528 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 69206528 = ⟨1281075369, 1881184031⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_34603264]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71304192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71304192 = ⟨226919109, 591805476⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35652096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_71827584 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 71827584 = ⟨803357691, 2069584533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_35913792]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76021888 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76021888 = ⟨496425209, 1728396691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38010944]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_76546304 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 76546304 = ⟨714436044, 537668815⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_38273152]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_80216192 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 80216192 = ⟨1100540130, 255527593⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_40108096]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84410496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84410496 = ⟨1637034951, 1798133725⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42205248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_84934912 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 84934912 = ⟨776417994, 1030749483⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42467456]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_85983744 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 85983744 = ⟨188920517, 129084268⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_42991872]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_88604800 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 88604800 = ⟨1747594197, 209227903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_44302400]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_92799104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 92799104 = ⟨1681538406, 1129913956⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46399552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_93323520 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 93323520 = ⟨94977371, 944044403⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_46661760]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_96993408 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 96993408 = ⟨1023034171, 182233744⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_48496704]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101187712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101187712 = ⟨1011175259, 645182681⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50593856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_101712128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 101712128 = ⟨848401480, 718945754⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_50856064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_102760960 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 102760960 = ⟨1749908167, 942884683⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_51380480]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_104858624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 104858624 = ⟨1988413837, 422428418⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52429312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_105382016 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 105382016 = ⟨487695512, 1223946656⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_52691008]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_109576320 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 109576320 = ⟨1010417682, 1282137820⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_54788160]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_110100736 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 110100736 = ⟨2071745643, 271354250⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_55050368]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_113770624 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 113770624 = ⟨1612555574, 1930076179⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_56885312]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_117964928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 117964928 = ⟨1355854337, 718824790⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_58982464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_118489344 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 118489344 = ⟨1678702104, 98729089⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59244672]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_119538176 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 119538176 = ⟨400611641, 2054250668⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_59769088]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_122159232 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 122159232 = ⟨202061559, 2078786582⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_61079616]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126353536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126353536 = ⟨403747547, 1586018672⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63176768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_126877952 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 126877952 = ⟨2110968077, 1420727144⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_63438976]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_130547840 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 130547840 = ⟨2073592755, 1273950686⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_65273920]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_135266560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 135266560 = ⟨1165378628, 56576614⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_67633280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_136315392 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 136315392 = ⟨1351271308, 420259353⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_68157696]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_138413056 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 138413056 = ⟨966963960, 791773240⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_69206528]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_143655168 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 143655168 = ⟨709239802, 938267219⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_71827584]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_152043776 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 152043776 = ⟨1494244494, 1711212903⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76021888]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_153092608 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 153092608 = ⟨2037658142, 467173539⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_76546304]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_160432384 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 160432384 = ⟨196138344, 1910340828⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_80216192]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_168820992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 168820992 = ⟨1288722562, 1631061559⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84410496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_169869824 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 169869824 = ⟨1035319038, 1105668817⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_84934912]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_171967488 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 171967488 = ⟨852511271, 383685221⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_85983744]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_177209600 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 177209600 = ⟨475244720, 1864581069⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_88604800]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_185598208 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 185598208 = ⟨1054457382, 1917347980⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_92799104]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_186647040 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 186647040 = ⟨1043672527, 1018844499⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_93323520]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_193986816 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 193986816 = ⟨1273032669, 781670314⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_96993408]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_202375424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 202375424 = ⟨1209062539, 935825235⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101187712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_203424256 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 203424256 = ⟨115043157, 1293341871⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_101712128]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_205521920 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 205521920 = ⟨925678133, 1851895798⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_102760960]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_210764032 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 210764032 = ⟨2033858181, 665228263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_105382016]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_219152640 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 219152640 = ⟨1223327429, 861367626⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_109576320]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_220201472 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 220201472 = ⟨1497341813, 945982801⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_110100736]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_227541248 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 227541248 = ⟨1108233253, 1810317290⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_113770624]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_235929856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 235929856 = ⟨550972811, 1685493707⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_117964928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_236978688 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 236978688 = ⟨1255344394, 1359906533⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_118489344]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_239076352 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 239076352 = ⟨1024200565, 2131726269⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_119538176]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_244318464 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 244318464 = ⟨1548909364, 1630197111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_122159232]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_252707072 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 252707072 = ⟨1505171760, 827913608⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126353536]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_253755904 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 253755904 = ⟨594717788, 864465383⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_126877952]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_261095680 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 261095680 = ⟨1129382909, 1509137675⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_130547840]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_270533120 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 270533120 = ⟨489439710, 2144775599⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_135266560]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_272630784 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 272630784 = ⟨905527003, 2103042246⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_136315392]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_287310336 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 287310336 = ⟨259587166, 1650602136⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_143655168]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_304087552 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 304087552 = ⟨1516127009, 1317089947⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_152043776]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_306185216 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 306185216 = ⟨142321536, 2005775263⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_153092608]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_320864768 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 320864768 = ⟨602875507, 1091057915⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_160432384]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_337641984 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 337641984 = ⟨535084156, 2000364484⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_168820992]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_339739648 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 339739648 = ⟨1601482956, 1555011007⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_169869824]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_354419200 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 354419200 = ⟨790139636, 2085846126⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_177209600]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_371196416 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 371196416 = ⟨1628020864, 1715589093⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_185598208]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_373294080 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 373294080 = ⟨1145573298, 2059018920⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_186647040]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_387973632 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 387973632 = ⟨485691986, 1136255632⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_193986816]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_404750848 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 404750848 = ⟨886237591, 1900431489⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_202375424]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_406848512 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 406848512 = ⟨429418708, 1721759118⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_203424256]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_421528064 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 421528064 = ⟨1499534668, 658645604⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_210764032]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_438305280 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 438305280 = ⟨1894252444, 971605041⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_219152640]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_440402944 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 440402944 = ⟨1850100142, 606004238⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_220201472]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_455082496 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 455082496 = ⟨1100053231, 331480709⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_227541248]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_471859712 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 471859712 = ⟨537023474, 883770939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_235929856]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_473957376 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 473957376 = ⟨890643854, 2061547316⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_236978688]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_488636928 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 488636928 = ⟨375624098, 1995300642⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_244318464]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_505414144 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 505414144 = ⟨1207442401, 1055753787⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_252707072]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_507511808 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 507511808 = ⟨1335475227, 1076118019⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_253755904]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_522191360 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 522191360 = ⟨790746873, 46501908⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_261095680]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_541066240 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 541066240 = ⟨265368403, 1358284640⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_270533120]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_574620672 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 574620672 = ⟨764411913, 101707538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_287310336]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_608175104 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 608175104 = ⟨591805476, 1920564538⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_304087552]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_641729536 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 641729536 = ⟨422428418, 159069810⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_320864768]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_675283968 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 675283968 = ⟨791773240, 1180519687⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_337641984]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_708838400 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 708838400 = ⟨383685221, 1294972376⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_354419200]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_742392832 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 742392832 = ⟨1851895798, 1221805514⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_371196416]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_775947264 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 775947264 = ⟨2131726269, 1123283082⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_387973632]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_809501696 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 809501696 = ⟨2103042246, 1241956644⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_404750848]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_843056128 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 843056128 = ⟨2005775263, 2005162111⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_421528064]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_876610560 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 876610560 = ⟨1555011007, 546000691⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_438305280]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_910164992 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 910164992 = ⟨2059018920, 1001910349⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_455082496]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_943719424 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 943719424 = ⟨1721759118, 1718064939⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_471859712]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_977273856 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 977273856 = ⟨606004238, 297383505⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_488636928]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1010828288 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1010828288 = ⟨2061547316, 1256839793⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_505414144]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem power_1044382720 : R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen 1044382720 = ⟨1076118019, 812008420⟩ := by
  conv_lhs => rw [fastPow_succ]
  rw [power_522191360]
  norm_num [R17TableBasePowerProbe.cmul, R17TableBasePowerProbe.addM,
    R17TableBasePowerProbe.subM, R17TableBasePowerProbe.gen]

theorem entry_00 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 128) = ⟨789199007, 265368403⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 128 = 4195328 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_4195328

theorem entry_00_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨789199007, 265368403⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 128) := by
  rw [← entry_00]
  exact fastPow_decode_zPow _

theorem entry_01 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 129) = ⟨265368403, 1358284640⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 129 = 541066240 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_541066240

theorem entry_01_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨265368403, 1358284640⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 129) := by
  rw [← entry_01]
  exact fastPow_decode_zPow _

theorem entry_02 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 130) = ⟨905527003, 2103042246⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 130 = 272630784 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_272630784

theorem entry_02_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨905527003, 2103042246⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 130) := by
  rw [← entry_02]
  exact fastPow_decode_zPow _

theorem entry_03 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 131) = ⟨2103042246, 1241956644⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 131 = 809501696 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_809501696

theorem entry_03_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2103042246, 1241956644⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 131) := by
  rw [← entry_03]
  exact fastPow_decode_zPow _

theorem entry_04 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 132) = ⟨966963960, 791773240⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 132 = 138413056 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_138413056

theorem entry_04_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨966963960, 791773240⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 132) := by
  rw [← entry_04]
  exact fastPow_decode_zPow _

theorem entry_05 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 133) = ⟨791773240, 1180519687⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 133 = 675283968 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_675283968

theorem entry_05_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨791773240, 1180519687⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 133) := by
  rw [← entry_05]
  exact fastPow_decode_zPow _

theorem entry_06 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 134) = ⟨429418708, 1721759118⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 134 = 406848512 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_406848512

theorem entry_06_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨429418708, 1721759118⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 134) := by
  rw [← entry_06]
  exact fastPow_decode_zPow _

theorem entry_07 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 135) = ⟨1721759118, 1718064939⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 135 = 943719424 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_943719424

theorem entry_07_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1721759118, 1718064939⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 135) := by
  rw [← entry_07]
  exact fastPow_decode_zPow _

theorem entry_08 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 136) = ⟨226919109, 591805476⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 136 = 71304192 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_71304192

theorem entry_08_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨226919109, 591805476⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 136) := by
  rw [← entry_08]
  exact fastPow_decode_zPow _

theorem entry_09 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 137) = ⟨591805476, 1920564538⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 137 = 608175104 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_608175104

theorem entry_09_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨591805476, 1920564538⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 137) := by
  rw [← entry_09]
  exact fastPow_decode_zPow _

theorem entry_10 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 138) = ⟨1601482956, 1555011007⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 138 = 339739648 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_339739648

theorem entry_10_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1601482956, 1555011007⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 138) := by
  rw [← entry_10]
  exact fastPow_decode_zPow _

theorem entry_11 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 139) = ⟨1555011007, 546000691⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 139 = 876610560 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_876610560

theorem entry_11_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1555011007, 546000691⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 139) := by
  rw [← entry_11]
  exact fastPow_decode_zPow _

theorem entry_12 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 140) = ⟨925678133, 1851895798⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 140 = 205521920 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_205521920

theorem entry_12_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨925678133, 1851895798⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 140) := by
  rw [← entry_12]
  exact fastPow_decode_zPow _

theorem entry_13 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 141) = ⟨1851895798, 1221805514⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 141 = 742392832 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_742392832

theorem entry_13_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1851895798, 1221805514⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 141) := by
  rw [← entry_13]
  exact fastPow_decode_zPow _

theorem entry_14 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 142) = ⟨890643854, 2061547316⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 142 = 473957376 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_473957376

theorem entry_14_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨890643854, 2061547316⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 142) := by
  rw [← entry_14]
  exact fastPow_decode_zPow _

theorem entry_15 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 143) = ⟨2061547316, 1256839793⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 143 = 1010828288 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1010828288

theorem entry_15_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2061547316, 1256839793⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 143) := by
  rw [← entry_15]
  exact fastPow_decode_zPow _

theorem entry_16 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 144) = ⟨2045776109, 764411913⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 144 = 37749760 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_37749760

theorem entry_16_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2045776109, 764411913⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 144) := by
  rw [← entry_16]
  exact fastPow_decode_zPow _

theorem entry_17 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 145) = ⟨764411913, 101707538⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 145 = 574620672 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_574620672

theorem entry_17_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨764411913, 101707538⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 145) := by
  rw [← entry_17]
  exact fastPow_decode_zPow _

theorem entry_18 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 146) = ⟨142321536, 2005775263⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 146 = 306185216 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_306185216

theorem entry_18_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨142321536, 2005775263⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 146) := by
  rw [← entry_18]
  exact fastPow_decode_zPow _

theorem entry_19 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 147) = ⟨2005775263, 2005162111⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 147 = 843056128 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_843056128

theorem entry_19_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2005775263, 2005162111⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 147) := by
  rw [← entry_19]
  exact fastPow_decode_zPow _

theorem entry_20 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 148) = ⟨852511271, 383685221⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 148 = 171967488 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_171967488

theorem entry_20_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨852511271, 383685221⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 148) := by
  rw [← entry_20]
  exact fastPow_decode_zPow _

theorem entry_21 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 149) = ⟨383685221, 1294972376⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 149 = 708838400 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_708838400

theorem entry_21_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨383685221, 1294972376⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 149) := by
  rw [← entry_21]
  exact fastPow_decode_zPow _

theorem entry_22 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 150) = ⟨1850100142, 606004238⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 150 = 440402944 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_440402944

theorem entry_22_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1850100142, 606004238⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 150) := by
  rw [← entry_22]
  exact fastPow_decode_zPow _

theorem entry_23 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 151) = ⟨606004238, 297383505⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 151 = 977273856 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_977273856

theorem entry_23_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨606004238, 297383505⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 151) := by
  rw [← entry_23]
  exact fastPow_decode_zPow _

theorem entry_24 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 152) = ⟨1988413837, 422428418⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 152 = 104858624 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_104858624

theorem entry_24_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1988413837, 422428418⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 152) := by
  rw [← entry_24]
  exact fastPow_decode_zPow _

theorem entry_25 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 153) = ⟨422428418, 159069810⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 153 = 641729536 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_641729536

theorem entry_25_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨422428418, 159069810⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 153) := by
  rw [← entry_25]
  exact fastPow_decode_zPow _

theorem entry_26 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 154) = ⟨1145573298, 2059018920⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 154 = 373294080 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_373294080

theorem entry_26_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1145573298, 2059018920⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 154) := by
  rw [← entry_26]
  exact fastPow_decode_zPow _

theorem entry_27 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 155) = ⟨2059018920, 1001910349⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 155 = 910164992 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_910164992

theorem entry_27_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2059018920, 1001910349⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 155) := by
  rw [← entry_27]
  exact fastPow_decode_zPow _

theorem entry_28 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 156) = ⟨1024200565, 2131726269⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 156 = 239076352 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_239076352

theorem entry_28_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1024200565, 2131726269⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 156) := by
  rw [← entry_28]
  exact fastPow_decode_zPow _

theorem entry_29 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 157) = ⟨2131726269, 1123283082⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 157 = 775947264 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_775947264

theorem entry_29_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨2131726269, 1123283082⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 157) := by
  rw [← entry_29]
  exact fastPow_decode_zPow _

theorem entry_30 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 158) = ⟨1335475227, 1076118019⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 158 = 507511808 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_507511808

theorem entry_30_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1335475227, 1076118019⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 158) := by
  rw [← entry_30]
  exact fastPow_decode_zPow _

theorem entry_31 :
    R17TableBasePowerProbe.fastPow R17TableBasePowerProbe.gen
      (R17TableExponentDomainBridge.leftExponent 159) = ⟨1076118019, 812008420⟩ := by
  have hexp : R17TableExponentDomainBridge.leftExponent 159 = 1044382720 := by
    norm_num [R17TableExponentDomainBridge.leftExponent, R17MinimalReverseBits.reverseBits]
  rw [hexp]
  exact power_1044382720

theorem entry_31_zPow :
    R17TableBasePowerBridge.decode
        (toNatC (⟨1076118019, 812008420⟩ : R17TableBasePowerProbe.C)) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode (toNatC R17TableBasePowerProbe.gen))
        (R17TableExponentDomainBridge.leftExponent 159) := by
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

end R17TableAChunk04Certificate
