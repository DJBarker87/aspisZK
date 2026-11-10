import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p12
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le at' K Lane frontierLoop decodeLane)

/-! ## 11. reference side: a failing header guard returns Err -/

theorem hl_ne (b : Slice U8) (h : ¬ b.val.length = 768) : (Slice.len b != 768#usize) = true := by
  apply bne_iff_ne.2
  intro e
  apply h
  have := congrArg UScalar.val e
  simpa [Slice.len_val, Slice.length] using this

theorem hl_eq (b : Slice U8) (h : b.val.length = 768) : (Slice.len b != 768#usize) = false := by
  rw [bne_eq_false_iff_eq]
  apply UScalar.eq_of_val_eq
  simp [Slice.len_val, Slice.length, h]

theorem idx_g (b : Slice U8) (i : Usize) (h : i.val < b.val.length) :
    b.index_usize i = ok (g b i.val) := by
  rw [idx_slice b i h]
  unfold g
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem ref_hdr_bad (b : Slice U8) (h : ¬ HdrOK b) :
    NCV_Reference.decode_lane_ref b = ok (core.result.Result.Err ()) := by
  unfold HdrOK at h
  by_cases p0 : b.val.length = 768
  swap
  · unfold NCV_Reference.decode_lane_ref
    simp only [hl_ne b p0, if_true]
  have hl := hl_eq b p0
  have v4 : (4#usize).val = 4 := by simp
  have v5 : (5#usize).val = 5 := by simp
  have v6 : (6#usize).val = 6 := by simp
  have v7 : (7#usize).val = 7 := by simp
  have v8 : (8#usize).val = 8 := by simp
  have v40 : (40#usize).val = 40 := by simp
  have v73 : (73#usize).val = 73 := by simp
  have v80 : (80#usize).val = 80 := by simp
  obtain ⟨s, hs, hsv⟩ := idx_to b 4#usize (by rw [v4]; omega)
  rw [v4] at hsv
  have g4 := idx_g b 4#usize (by rw [v4]; omega)
  have g5 := idx_g b 5#usize (by rw [v5]; omega)
  have g6 := idx_g b 6#usize (by rw [v6]; omega)
  have g7 := idx_g b 7#usize (by rw [v7]; omega)
  rw [v4] at g4
  rw [v5] at g5
  rw [v6] at g6
  rw [v7] at g7
  have e1 : NCV_Reference.equal s (Array.to_slice (Array.make 4#usize [65#u8, 83#u8, 76#u8, 56#u8])) =
      ok (decide (slg b.val 0 4 = mag)) := by
    rw [equal_eq, hsv]; rfl
  by_cases p1 : slg b.val 0 4 = mag
  swap
  · have d1 : decide (slg b.val 0 4 = mag) = false := by simp [p1]
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1]
  by_cases p2 : g b 4 = 2#u8
  swap
  · have n2 : (g b 4 != 2#u8) = true := bne_iff_ne.2 p2
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
      p1, if_true, g4, n2]
  by_cases p3 : (g b 5).val < 8
  swap
  · have n3 : g b 5 ≥ 8#u8 := by scalar_tac
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
      p1, if_true, g4, g5, bne_eq_false_iff_eq.2 p2, n3]
  by_cases p4 : g b 6 = 8#u8
  swap
  · have n4 : (g b 6 != 8#u8) = true := bne_iff_ne.2 p4
    have n3 : ¬ g b 5 ≥ 8#u8 := by scalar_tac
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
      p1, if_true, g4, g5, g6, bne_eq_false_iff_eq.2 p2, n3, n4]
  by_cases p5 : g b 7 = 20#u8
  swap
  · have n5 : (g b 7 != 20#u8) = true := bne_iff_ne.2 p5
    have n3 : ¬ g b 5 ≥ 8#u8 := by scalar_tac
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
      p1, if_true, g4, g5, g6, g7, bne_eq_false_iff_eq.2 p2, n3, bne_eq_false_iff_eq.2 p4, n5]
  obtain ⟨s2, hs2, hs2v⟩ := idx_range b 8#usize 40#usize (by rw [v8, v40]; omega) (by rw [v40]; omega)
  rw [v8, v40] at hs2v
  have e2 : NCV_Reference.equal s2 (Array.to_slice NCV_Reference.BINDING) =
      ok (decide (slg b.val 8 40 = NCV_Reference.BINDING.val)) := by
    rw [equal_eq, hs2v]; rfl
  by_cases p6 : slg b.val 8 40 = NCV_Reference.BINDING.val
  swap
  · have d2 : decide (slg b.val 8 40 = NCV_Reference.BINDING.val) = false := by simp [p6]
    have n3 : ¬ g b 5 ≥ 8#u8 := by scalar_tac
    unfold NCV_Reference.decode_lane_ref
    simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
      p1, if_true, g4, g5, g6, g7, bne_eq_false_iff_eq.2 p2, n3, bne_eq_false_iff_eq.2 p4,
      bne_eq_false_iff_eq.2 p5, hs2, e2, d2]
  have p7 : ¬ Zs (slg b.val 73 80) := fun hz => h ⟨p0, p1, p2, p3, p4, p5, p6, hz⟩
  obtain ⟨s4, hs4, hs4v⟩ := idx_range b 73#usize 80#usize (by rw [v73, v80]; omega) (by rw [v80]; omega)
  rw [v73, v80] at hs4v
  have z4 : NCV_Reference.zero s4 = ok (decide (Zs (slg b.val 73 80))) := by
    rw [zero_eq, hs4v]; rfl
  have d4 : decide (Zs (slg b.val 73 80)) = false := by simp [p7]
  have d2 : decide (slg b.val 8 40 = NCV_Reference.BINDING.val) = true := by simp [p6]
  have n3 : ¬ g b 5 ≥ 8#u8 := by scalar_tac
  unfold NCV_Reference.decode_lane_ref
  simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, decide_true_eq_true,
    p1, if_true, g4, g5, g6, g7, bne_eq_false_iff_eq.2 p2, n3, bne_eq_false_iff_eq.2 p4,
    bne_eq_false_iff_eq.2 p5, hs2, e2, d2, hs4, z4, d4]

#print axioms ref_hdr_bad

end PCVY_Op50
