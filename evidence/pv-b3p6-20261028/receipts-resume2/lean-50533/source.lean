import PV_B3P_LayoutOffsets226
import PV_B3P_DigestValue226V3
import PV_B3P_FrontierOutcome226V3
namespace PV_B3P_LateRegions226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_LayoutOffsets226
set_option autoImplicit false
theorem recipient (p : reference226.OwnedPublic) (i : Usize)
    (hw : p.withdrawal = false)
    (lo : 70 ≤ i.val) (hi : i.val < 102) :
    reference226.byte_at p i = PV_B3P_DigestTotal226V3.digestAt p.recipient (Usize.wrapping_sub i 70#usize) := by
  have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
  have h1 : ¬ (i = 0#usize) := by scalar_tac
  have h2 : ¬ (i < 33#usize) := by scalar_tac
  have h3 : ¬ (i < 65#usize) := by scalar_tac
  have h4 : ¬ (i < 69#usize) := by scalar_tac
  have h5 : ¬ (i = 69#usize) := by scalar_tac
  have h6 : i < 102#usize := by scalar_tac
  simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
#print axioms recipient
theorem change (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 70 else 102) ≤ i.val) (hi : i.val < (if p.withdrawal then 102 else 134)) :
    reference226.byte_at p i = PV_B3P_DigestTotal226V3.digestAt p.change (Usize.wrapping_sub i (if p.withdrawal then 70#usize else 102#usize)) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 102#usize) := by scalar_tac
    have h7 : i < 134#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 70#usize) := by scalar_tac
    have h7 : i < 102#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
#print axioms change
theorem frontier (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 115 else 143) ≤ i.val) (hi : i.val < (if p.withdrawal then 755 else 783)) :
    reference226.byte_at p i = PV_B3P_FrontierOutcome226V3.frontierAt p.frontier (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 102#usize) := by scalar_tac
    have h7 : ¬ (i < 134#usize) := by scalar_tac
    have h8 : ¬ (i = 134#usize) := by scalar_tac
    have h9 : ¬ (i < 135#usize) := by scalar_tac
    have h10 : ¬ (i < 143#usize) := by scalar_tac
    have h11 : i < 783#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 70#usize) := by scalar_tac
    have h7 : ¬ (i < 102#usize) := by scalar_tac
    have h8 : ¬ (i = 102#usize) := by scalar_tac
    have h9 : ¬ (i < 107#usize) := by scalar_tac
    have h10 : ¬ (i < 115#usize) := by scalar_tac
    have h11 : i < 755#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
#print axioms frontier
theorem next_root (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 755 else 783) ≤ i.val) (hi : i.val < (if p.withdrawal then 787 else 815)) :
    reference226.byte_at p i = PV_B3P_DigestTotal226V3.digestAt p.next_root (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 640#usize) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 102#usize) := by scalar_tac
    have h7 : ¬ (i < 134#usize) := by scalar_tac
    have h8 : ¬ (i = 134#usize) := by scalar_tac
    have h9 : ¬ (i < 135#usize) := by scalar_tac
    have h10 : ¬ (i < 143#usize) := by scalar_tac
    have h11 : ¬ (i < 783#usize) := by scalar_tac
    have h12 : i < 815#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 70#usize) := by scalar_tac
    have h7 : ¬ (i < 102#usize) := by scalar_tac
    have h8 : ¬ (i = 102#usize) := by scalar_tac
    have h9 : ¬ (i < 107#usize) := by scalar_tac
    have h10 : ¬ (i < 115#usize) := by scalar_tac
    have h11 : ¬ (i < 755#usize) := by scalar_tac
    have h12 : i < 787#usize := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
#print axioms next_root
theorem next_frontier (p : reference226.OwnedPublic) (i : Usize)
    (lo : (if p.withdrawal then 787 else 815) ≤ i.val) (hi : i.val < (if p.withdrawal then 1427 else 1455)) :
    reference226.byte_at p i = PV_B3P_FrontierOutcome226V3.frontierAt p.next_frontier (Usize.wrapping_sub (Usize.wrapping_sub i (if p.withdrawal then 115#usize else 143#usize)) 672#usize) := by
  cases hw : p.withdrawal with
  | false =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1455#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 102#usize) := by scalar_tac
    have h7 : ¬ (i < 134#usize) := by scalar_tac
    have h8 : ¬ (i = 134#usize) := by scalar_tac
    have h9 : ¬ (i < 135#usize) := by scalar_tac
    have h10 : ¬ (i < 143#usize) := by scalar_tac
    have h11 : ¬ (i < 783#usize) := by scalar_tac
    have h12 : ¬ (i < 815#usize) := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
  | true =>
    simp only [hw,Bool.false_eq_true,↓reduceIte] at lo hi ⊢
    have h0 : ¬ (i ≥ 1427#usize) := by scalar_tac
    have h1 : ¬ (i = 0#usize) := by scalar_tac
    have h2 : ¬ (i < 33#usize) := by scalar_tac
    have h3 : ¬ (i < 65#usize) := by scalar_tac
    have h4 : ¬ (i < 69#usize) := by scalar_tac
    have h5 : ¬ (i = 69#usize) := by scalar_tac
    have h6 : ¬ (i < 70#usize) := by scalar_tac
    have h7 : ¬ (i < 102#usize) := by scalar_tac
    have h8 : ¬ (i = 102#usize) := by scalar_tac
    have h9 : ¬ (i < 107#usize) := by scalar_tac
    have h10 : ¬ (i < 115#usize) := by scalar_tac
    have h11 : ¬ (i < 755#usize) := by scalar_tac
    have h12 : ¬ (i < 787#usize) := by scalar_tac
    simp only [reference226.byte_at,hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,PV_B3P_DigestTotal226V3.digestAt,PV_B3P_FrontierOutcome226V3.frontierAt]
#print axioms next_frontier
end PV_B3P_LateRegions226
