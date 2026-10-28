import R1Z.PV_RDB2C_PV_B2_D_RowRange
import R1Z.PV_RDB2C_PV_B2_D_SubValue
import R1Z.PV_RDB2C_PV_B2_D_PowTotal
set_option autoImplicit false
namespace PV_B2_D_RawTotal
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_ArrayTotal
theorem div16 (x : Usize) : ∃ q, (x / 16#usize : Result Usize) = ok q ∧ q.val = x.val / 16 := by
  have hs : (x / 16#usize : Result Usize) ⦃ q => q.val = x.val / 16 ⦄ := by
    apply Usize.div_spec
    decide
  exact WP.spec_imp_exists hs
#print axioms div16
theorem rem16 (x : Usize) : ∃ q, (x % 16#usize : Result Usize) = ok q ∧ q.val = x.val % 16 := by
  have hs : (x % 16#usize : Result Usize) ⦃ q => q.val = x.val % 16 ⦄ := by
    apply Usize.rem_spec
    decide
  exact WP.spec_imp_exists hs
#print axioms rem16
theorem div28 (x : Usize) : ∃ q, (x / 28#usize : Result Usize) = ok q ∧ q.val = x.val / 28 := by
  have hs : (x / 28#usize : Result Usize) ⦃ q => q.val = x.val / 28 ⦄ := by
    apply Usize.div_spec
    decide
  exact WP.spec_imp_exists hs
#print axioms div28
theorem rem28 (x : Usize) : ∃ q, (x % 28#usize : Result Usize) = ok q ∧ q.val = x.val % 28 := by
  have hs : (x % 28#usize : Result Usize) ⦃ q => q.val = x.val % 28 ⦄ := by
    apply Usize.rem_spec
    decide
  exact WP.spec_imp_exists hs
#print axioms rem28
theorem kind0 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 0#usize j) := by
  obtain ⟨r,hr,hbound⟩ := PV_B2_D_RowRange.source w.variant j hj
  obtain ⟨i,hi,hival⟩ := div16 r
  obtain ⟨d,hd,hdval⟩ := rem16 r
  have hib : i.val < (64#usize).val := by change i.val < 64; omega
  obtain ⟨mask,hm⟩ := read aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS i hib
  unfold host_weights.raw_value
  simp only [show (0#usize = 0#usize) = True from by decide,if_true,hr,hi,bind_tc_ok,hm,hd,lift]
  split <;> exact ⟨_,rfl⟩

theorem kind4 (w : host_weights.Weights) (j : Usize) :
    Total (host_weights.raw_value w 4#usize j) := by
  unfold host_weights.raw_value
  simp only [show (4#usize = 0#usize) = False from by decide,if_false,if_pos rfl]
  by_cases hj : j < 56#usize
  · rw [if_pos hj]
    obtain ⟨i,hi,hival⟩ := div28 j
    obtain ⟨d,hd,hdval⟩ := rem28 j
    have hib : i.val < (2#usize).val := by change j.val < 56 at hj; change i.val < 2; omega
    obtain ⟨q,hq⟩ := read w.extra i hib
    obtain ⟨out,ho⟩ := PV_B2_D_PowTotal.source q (UScalar.cast .U64 d)
    simp only [hi,hq,hd,lift,bind_tc_ok,ho]
    exact ⟨_,rfl⟩
  · rw [if_neg hj]
    exact ⟨_,rfl⟩
theorem kind1 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 1#usize j) := by
  have hb5 : (Usize.wrapping_sub 1#usize 1#usize).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors (Usize.wrapping_sub 1#usize 1#usize); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show (1#usize = 0#usize) = False from by decide,if_false,
    show (1#usize = 4#usize) = False from by decide,
    show (1#usize ≥ 1#usize) = True from by decide,if_true,
    show (1#usize ≤ 3#usize) = True from by decide,
    show (1#usize < 4#usize) = True from by decide]
  apply PV_B2_C_ArrayTotal.bind _ _ (by
    unfold transport.Variant.Insts.CoreCmpPartialEqVariant.eq
    exact ⟨_,rfl⟩)
  intro bit
  cases bit
  · simpa only [Bool.false_eq_true,if_false,bind_tc_ok] using ht
  · simp only [if_true,lift,bind_tc_ok]
    obtain ⟨r,hr,_⟩ := PV_B2_D_RowRange.source w.variant j hj
    have hb3 : (Usize.wrapping_sub 1#usize 1#usize).val < (3#usize).val := by
      rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
      scalar_tac
    apply PV_B2_C_ArrayTotal.bind _ _ ⟨r,hr⟩
    intro row
    exact PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb3) (fun p => PV_B2_D_RawHelpersTotal.point p row)
#print axioms kind1
theorem kind2 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 2#usize j) := by
  have hb5 : (Usize.wrapping_sub 2#usize 1#usize).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors (Usize.wrapping_sub 2#usize 1#usize); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show (2#usize = 0#usize) = False from by decide,if_false,
    show (2#usize = 4#usize) = False from by decide,
    show (2#usize ≥ 1#usize) = True from by decide,if_true,
    show (2#usize ≤ 3#usize) = True from by decide,
    show (2#usize < 4#usize) = True from by decide]
  apply PV_B2_C_ArrayTotal.bind _ _ (by
    unfold transport.Variant.Insts.CoreCmpPartialEqVariant.eq
    exact ⟨_,rfl⟩)
  intro bit
  cases bit
  · simpa only [Bool.false_eq_true,if_false,bind_tc_ok] using ht
  · simp only [if_true,lift,bind_tc_ok]
    obtain ⟨r,hr,_⟩ := PV_B2_D_RowRange.source w.variant j hj
    have hb3 : (Usize.wrapping_sub 2#usize 1#usize).val < (3#usize).val := by
      rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
      scalar_tac
    apply PV_B2_C_ArrayTotal.bind _ _ ⟨r,hr⟩
    intro row
    exact PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb3) (fun p => PV_B2_D_RawHelpersTotal.point p row)
#print axioms kind2
theorem kind3 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 3#usize j) := by
  have hb5 : (Usize.wrapping_sub 3#usize 1#usize).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors (Usize.wrapping_sub 3#usize 1#usize); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show (3#usize = 0#usize) = False from by decide,if_false,
    show (3#usize = 4#usize) = False from by decide,
    show (3#usize ≥ 1#usize) = True from by decide,if_true,
    show (3#usize ≤ 3#usize) = True from by decide,
    show (3#usize < 4#usize) = True from by decide]
  apply PV_B2_C_ArrayTotal.bind _ _ (by
    unfold transport.Variant.Insts.CoreCmpPartialEqVariant.eq
    exact ⟨_,rfl⟩)
  intro bit
  cases bit
  · simpa only [Bool.false_eq_true,if_false,bind_tc_ok] using ht
  · simp only [if_true,lift,bind_tc_ok]
    obtain ⟨r,hr,_⟩ := PV_B2_D_RowRange.source w.variant j hj
    have hb3 : (Usize.wrapping_sub 3#usize 1#usize).val < (3#usize).val := by
      rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
      scalar_tac
    apply PV_B2_C_ArrayTotal.bind _ _ ⟨r,hr⟩
    intro row
    exact PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb3) (fun p => PV_B2_D_RawHelpersTotal.point p row)
#print axioms kind3
theorem kind5 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 5#usize j) := by
  have hb5 : (Usize.wrapping_sub 5#usize 2#usize).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors (Usize.wrapping_sub 5#usize 2#usize); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show (5#usize = 0#usize) = False from by decide,if_false,
    show (5#usize = 4#usize) = False from by decide,
    show (5#usize ≥ 1#usize) = True from by decide,if_true,
    show (5#usize ≤ 3#usize) = False from by decide,
    show (5#usize < 4#usize) = False from by decide]
  exact ht
#print axioms kind5
theorem kind6 (w : host_weights.Weights) (j : Usize) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w 6#usize j) := by
  have hb5 : (Usize.wrapping_sub 6#usize 2#usize).val < (5#usize).val := by
    rw [PV_B2_D_SubValue.sub_val _ _ (by scalar_tac)]
    scalar_tac
  have ht : Total (do let a ← Array.index_usize w.factors (Usize.wrapping_sub 6#usize 2#usize); host_weights.tensor_raw a j) :=
    PV_B2_C_ArrayTotal.bind _ _ (read _ _ hb5) (fun a => PV_B2_D_RawHelpersTotal.tensor a j)
  unfold host_weights.raw_value
  simp only [show (6#usize = 0#usize) = False from by decide,if_false,
    show (6#usize = 4#usize) = False from by decide,
    show (6#usize ≥ 1#usize) = True from by decide,if_true,
    show (6#usize ≤ 3#usize) = False from by decide,
    show (6#usize < 4#usize) = False from by decide]
  exact ht
#print axioms kind6
theorem source (w : host_weights.Weights) (kind j : Usize)
    (hk : kind.val < 7) (hj : j.val < (1024#usize).val) :
    Total (host_weights.raw_value w kind j) := by
  have hc : kind=0#usize ∨ kind=1#usize ∨ kind=2#usize ∨ kind=3#usize ∨
      kind=4#usize ∨ kind=5#usize ∨ kind=6#usize := by scalar_tac
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact kind0 w j hj
  · exact kind1 w j hj
  · exact kind2 w j hj
  · exact kind3 w j hj
  · exact kind4 w j
  · exact kind5 w j hj
  · exact kind6 w j hj
#print axioms kind0
#print axioms kind4
#print axioms source
end PV_B2_D_RawTotal
