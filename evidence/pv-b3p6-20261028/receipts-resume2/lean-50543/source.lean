import PV_B3P_LayoutRegions226
import PV_B3P_DigestRegionValue226V3
import PV_B3P_LateValue226
import PV_B3P_ScalarValue226
namespace PV_B3P_ByteCellValue226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteLayout226V3
set_option autoImplicit false
attribute [local irreducible] layout fields frontier indexBytes
set_option backward.isDefEq.respectTransparency false in
theorem success_value (p : reference226.OwnedPublic) (i : Usize) (b : U8)
    (h : reference226.byte_at p i = .ok (.Ok b)) (hi : i.val < (layout p).length) :
    b = (layout p)[i.val]?.getD 0#u8 := by
  have hlen := layout_length p
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at hlen
    rw [hlen] at hi
    by_cases hb0 : i.val < 1
    ·
      have hlo : 0 ≤ i.val := by omega
      have hup : i.val < 1 := by omega
      rw [PV_B3P_LayoutRegions226.variant p i.val hlo hup]
      have hiEq : i = 0#usize := by apply UScalar.eq_of_val_eq; change i.val = 0; omega
      rw [hiEq,PV_B3P_Regions226V3.discriminant] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 0 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb1 : i.val < 33
    ·
      have hlo : 1 ≤ i.val := by omega
      have hup : i.val < 33 := by omega
      rw [PV_B3P_LayoutRegions226.anchor p i.val hlo hup]
      rw [PV_B3P_DigestRegionValue226V3.anchor p i hlo hup] at h
      rw [PV_B3P_Offset226V3.sub_value i 1#usize (by simpa using hlo)] at h
      split at h <;> cases h <;> rfl
    by_cases hb2 : i.val < 65
    ·
      have hlo : 33 ≤ i.val := by omega
      have hup : i.val < 65 := by omega
      rw [PV_B3P_LayoutRegions226.nullifier p i.val hlo hup]
      rw [PV_B3P_DigestRegionValue226V3.nullifier p i hlo hup] at h
      rw [PV_B3P_Offset226V3.sub_value i 33#usize (by simpa using hlo)] at h
      split at h <;> cases h <;> rfl
    by_cases hb3 : i.val < 69
    ·
      have hlo : 65 ≤ i.val := by omega
      have hup : i.val < 69 := by omega
      rw [PV_B3P_LayoutRegions226.asset p i.val hlo hup]
      rw [PV_B3P_ScalarValue226.asset p i hlo hup] at h
      split at h <;> cases h <;> rfl
    by_cases hb4 : i.val < 70
    ·
      have hlo : 69 ≤ i.val := by omega
      have hup : i.val < 70 := by omega
      rw [PV_B3P_LayoutRegions226.recipient_flag p i.val hlo hup]
      have hiEq : i = 69#usize := by apply UScalar.eq_of_val_eq; change i.val = 69; omega
      rw [hiEq,PV_B3P_ScalarRegions226.recipient_tag] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 69 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb5 : i.val < 102
    ·
      have hlo : 70 ≤ i.val := by omega
      have hup : i.val < 102 := by omega
      rw [PV_B3P_LayoutRegions226.recipient p i.val hw hlo hup]
      rw [PV_B3P_LateValue226.recipient p i hw hlo hup] at h
      split at h <;> cases h <;> rfl
    by_cases hb6 : i.val < 134
    ·
      have hlo : 102 ≤ i.val := by omega
      have hup : i.val < 134 := by omega
      rw [PV_B3P_LayoutRegions226.change p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.change p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    by_cases hb7 : i.val < 135
    ·
      have hlo : 134 ≤ i.val := by omega
      have hup : i.val < 135 := by omega
      rw [PV_B3P_LayoutRegions226.withdrawal_flag p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      have hiEq : i = 134#usize := by apply UScalar.eq_of_val_eq; change i.val = 134; omega
      have hid : i = (if p.withdrawal then 102#usize else 134#usize) := by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hiEq
      rw [hid,PV_B3P_ScalarRegions226.withdrawal_tag] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 134 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb8 : i.val < 143
    ·
      have hlo : 135 ≤ i.val := by omega
      have hup : i.val < 143 := by omega
      rw [PV_B3P_LayoutRegions226.index p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_ScalarValue226.index p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      exact (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    by_cases hb9 : i.val < 783
    ·
      have hlo : 143 ≤ i.val := by omega
      have hup : i.val < 783 := by omega
      rw [PV_B3P_LayoutRegions226.frontier p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.frontier p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    by_cases hb10 : i.val < 815
    ·
      have hlo : 783 ≤ i.val := by omega
      have hup : i.val < 815 := by omega
      rw [PV_B3P_LayoutRegions226.next_root p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.next_root p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    have hlo : 815 ≤ i.val := by omega
    have hup : i.val < 1455 := by omega
    rw [PV_B3P_LayoutRegions226.next_frontier p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
    rw [PV_B3P_LateValue226.next_frontier p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
    split at h <;> cases h <;> rfl
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at hlen
    rw [hlen] at hi
    by_cases hb0 : i.val < 1
    ·
      have hlo : 0 ≤ i.val := by omega
      have hup : i.val < 1 := by omega
      rw [PV_B3P_LayoutRegions226.variant p i.val hlo hup]
      have hiEq : i = 0#usize := by apply UScalar.eq_of_val_eq; change i.val = 0; omega
      rw [hiEq,PV_B3P_Regions226V3.discriminant] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 0 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb1 : i.val < 33
    ·
      have hlo : 1 ≤ i.val := by omega
      have hup : i.val < 33 := by omega
      rw [PV_B3P_LayoutRegions226.anchor p i.val hlo hup]
      rw [PV_B3P_DigestRegionValue226V3.anchor p i hlo hup] at h
      rw [PV_B3P_Offset226V3.sub_value i 1#usize (by simpa using hlo)] at h
      split at h <;> cases h <;> rfl
    by_cases hb2 : i.val < 65
    ·
      have hlo : 33 ≤ i.val := by omega
      have hup : i.val < 65 := by omega
      rw [PV_B3P_LayoutRegions226.nullifier p i.val hlo hup]
      rw [PV_B3P_DigestRegionValue226V3.nullifier p i hlo hup] at h
      rw [PV_B3P_Offset226V3.sub_value i 33#usize (by simpa using hlo)] at h
      split at h <;> cases h <;> rfl
    by_cases hb3 : i.val < 69
    ·
      have hlo : 65 ≤ i.val := by omega
      have hup : i.val < 69 := by omega
      rw [PV_B3P_LayoutRegions226.asset p i.val hlo hup]
      rw [PV_B3P_ScalarValue226.asset p i hlo hup] at h
      split at h <;> cases h <;> rfl
    by_cases hb4 : i.val < 70
    ·
      have hlo : 69 ≤ i.val := by omega
      have hup : i.val < 70 := by omega
      rw [PV_B3P_LayoutRegions226.recipient_flag p i.val hlo hup]
      have hiEq : i = 69#usize := by apply UScalar.eq_of_val_eq; change i.val = 69; omega
      rw [hiEq,PV_B3P_ScalarRegions226.recipient_tag] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 69 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb5 : i.val < 102
    ·
      have hlo : 70 ≤ i.val := by omega
      have hup : i.val < 102 := by omega
      rw [PV_B3P_LayoutRegions226.change p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.change p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    by_cases hb6 : i.val < 103
    ·
      have hlo : 102 ≤ i.val := by omega
      have hup : i.val < 103 := by omega
      rw [PV_B3P_LayoutRegions226.withdrawal_flag p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      have hiEq : i = 102#usize := by apply UScalar.eq_of_val_eq; change i.val = 102; omega
      have hid : i = (if p.withdrawal then 102#usize else 134#usize) := by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hiEq
      rw [hid,PV_B3P_ScalarRegions226.withdrawal_tag] at h
      have hv := (core.result.Result.Ok.inj (Result.ok.inj h)).symm
      have hzero : i.val - 102 = 0 := by omega
      simpa only [hw,Bool.false_eq_true,↓reduceIte,hzero,Nat.sub_zero,List.getElem?_cons_zero,Option.getD_some] using hv
    by_cases hb7 : i.val < 107
    ·
      have hlo : 103 ≤ i.val := by omega
      have hup : i.val < 107 := by omega
      rw [PV_B3P_LayoutRegions226.amount p i.val hw hlo hup]
      rw [PV_B3P_ScalarValue226.amount p i hw hlo hup] at h
      split at h <;> cases h <;> rfl
    by_cases hb8 : i.val < 115
    ·
      have hlo : 107 ≤ i.val := by omega
      have hup : i.val < 115 := by omega
      rw [PV_B3P_LayoutRegions226.index p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_ScalarValue226.index p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      exact (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    by_cases hb9 : i.val < 755
    ·
      have hlo : 115 ≤ i.val := by omega
      have hup : i.val < 755 := by omega
      rw [PV_B3P_LayoutRegions226.frontier p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.frontier p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    by_cases hb10 : i.val < 787
    ·
      have hlo : 755 ≤ i.val := by omega
      have hup : i.val < 787 := by omega
      rw [PV_B3P_LayoutRegions226.next_root p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
      rw [PV_B3P_LateValue226.next_root p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
      split at h <;> cases h <;> rfl
    have hlo : 787 ≤ i.val := by omega
    have hup : i.val < 1427 := by omega
    rw [PV_B3P_LayoutRegions226.next_frontier p i.val (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)]
    rw [PV_B3P_LateValue226.next_frontier p i (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hlo) (by simpa only [hw,Bool.false_eq_true,↓reduceIte] using hup)] at h
    split at h <;> cases h <;> rfl
#print axioms success_value
end PV_B3P_ByteCellValue226
