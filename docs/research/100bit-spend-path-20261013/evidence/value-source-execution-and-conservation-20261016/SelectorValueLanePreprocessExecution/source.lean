import SelectorValueLaneLoops012Slice
import SelectorValueLaneLoop0CanonicalOpenings
import SelectorValueLaneLoop1CanonicalOpenings
import SelectorValueLaneLoop2CanonicalOpenings
import ExtractedMaskQM31SquareExact
import EqualityValueAdapter
import SelectorValueLanePreprocessZeroInit
import SelectorValueLanePreprocessCanonical

/-! Source execution of the three 10-step preprocessing loops. Canonical
opening arrays suffice to derive every checked read, field operation, update,
and increment; the source loops are not assumed to succeed. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePreprocessExecution

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop0 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
abbrev Loop1 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
abbrev Loop2 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2

private theorem index_usize_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem index10_usize_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) :=
  index_usize_ok a i hi

theorem increment_success (i : Usize) (hi : i.val < 10) :
    ∃ i1 : Usize, UScalar.add i 1#usize = .ok i1 ∧ i1.val = i.val + 1 := by
  have hspec : (i + 1#usize : Result Usize) ⦃ z => z.val = i.val + 1 ⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i1, hrun, hval⟩ := WP.spec_imp_exists hspec
  change UScalar.add i 1#usize = .ok i1 at hrun
  exact ⟨i1, hrun, hval⟩

/-- All checked operations in loop 0 succeed from a canonical `z` view. -/
theorem loop0_success_fuel
    (fuel : Nat) (openings : Openings) (range : Array QM 33#usize)
    (index : Usize) (hspan : index.val + fuel = 10)
    (hopen : CanonicalArray openings.z) :
    ∃ outOpen outRange, Loop0 openings range index = .ok (outOpen, outRange) ∧
      outOpen = openings := by
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨openings, range, ?_, rfl⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range index = .ok (openings, range)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0.eq_def]
      simp only [if_neg hstop]
  | succ fuel ih =>
      have hindex : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hindex16 : index.val < 16 := Nat.lt_trans hindex (by decide)
      have hread : Array.index_usize openings.z index =
          .ok (openings.z.val[index.val]'(by simpa [openings.z.property] using
            hindex16)) :=
        index_usize_ok openings.z index hindex16
      have hq : Canonical (openings.z.val[index.val]'(by
          simpa [openings.z.property] using hindex16)) :=
        hopen ⟨index.val, by simpa [openings.z.property] using
          hindex16⟩
      obtain ⟨q1, hsq, hq1, _hsqv⟩ :=
        AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
          (openings.z.val[index.val]'(by simpa [openings.z.property] using
            hindex16)) hq
      obtain ⟨q2, hsub, _hq2, _hsubv⟩ :=
        AspisR1.EqualityValueAdapter.current_qm_sub_exact q1
          (openings.z.val[index.val]'(by simpa [openings.z.property] using
            hindex16)) hq1 hq
      obtain ⟨range1, hupdate, _hset⟩ := WP.spec_imp_exists
        (Array.update_spec range index q2 (by
          have hb : index.val < 33 := by omega
          simpa [range.property] using hb))
      obtain ⟨index1, hadd, hindex1⟩ := increment_success index hindex
      obtain ⟨outOpen, outRange, hrun, hopenOut⟩ :=
        ih range1 index1 (by omega)
      refine ⟨outOpen, outRange, ?_, hopenOut⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range index = .ok (outOpen, outRange)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range1 index1) =
        .ok (outOpen, outRange)
      rw [hadd, bind_tc_ok]
      exact hrun

/-- All checked operations in loop 1 succeed from a canonical `succ_z` view. -/
theorem loop1_success_fuel
    (fuel : Nat) (openings : Openings) (range : Array QM 33#usize)
    (index : Usize) (hspan : index.val + fuel = 10)
    (hopen : CanonicalArray openings.succ_z) :
    ∃ outOpen outRange, Loop1 openings range index = .ok (outOpen, outRange) ∧
      outOpen = openings := by
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨openings, range, ?_, rfl⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range index = .ok (openings, range)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1.eq_def]
      simp only [if_neg hstop]
  | succ fuel ih =>
      have hindex : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hindex16 : index.val < 16 := Nat.lt_trans hindex (by decide)
      have hread : Array.index_usize openings.succ_z index =
          .ok (openings.succ_z.val[index.val]'(by simpa [openings.succ_z.property] using
            hindex16)) :=
        index_usize_ok openings.succ_z index hindex16
      have hq : Canonical (openings.succ_z.val[index.val]'(by
          simpa [openings.succ_z.property] using hindex16)) :=
        hopen ⟨index.val, by simpa [openings.succ_z.property] using
          hindex16⟩
      obtain ⟨q1, hsq, hq1, _hsqv⟩ :=
        AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
          (openings.succ_z.val[index.val]'(by simpa [openings.succ_z.property] using
            hindex16)) hq
      obtain ⟨q2, hsub, _hq2, _hsubv⟩ :=
        AspisR1.EqualityValueAdapter.current_qm_sub_exact q1
          (openings.succ_z.val[index.val]'(by simpa [openings.succ_z.property] using
            hindex16)) hq1 hq
      have haddOffsetSpec : (10#usize + index : Result Usize)
          ⦃ dest => dest.val = 10 + index.val ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨dest, hoffset, hdest⟩ := WP.spec_imp_exists haddOffsetSpec
      obtain ⟨range1, hupdate, _hset⟩ := WP.spec_imp_exists
        (Array.update_spec range dest q2 (by simpa [range.property, hdest] using
          (show 10 + index.val < 33 by omega)))
      obtain ⟨index1, hadd, hindex1⟩ := increment_success index hindex
      obtain ⟨outOpen, outRange, hrun, hopenOut⟩ :=
        ih range1 index1 (by omega)
      refine ⟨outOpen, outRange, ?_, hopenOut⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range index = .ok (outOpen, outRange)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hoffset, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range1 index1) =
        .ok (outOpen, outRange)
      rw [hadd, bind_tc_ok]
      exact hrun

/-- All checked operations in loop 2 succeed from a canonical `xor12_z` view. -/
theorem loop2_success_fuel
    (fuel : Nat) (openings : Openings) (range : Array QM 33#usize)
    (index : Usize) (hspan : index.val + fuel = 10)
    (hopen : CanonicalArray openings.xor12_z) :
    ∃ outOpen outRange, Loop2 openings range index = .ok (outOpen, outRange) ∧
      outOpen = openings := by
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨openings, range, ?_, rfl⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (openings, range)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def]
      simp only [if_neg hstop]
  | succ fuel ih =>
      have hindex : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hindex16 : index.val < 16 := Nat.lt_trans hindex (by decide)
      have hread : Array.index_usize openings.xor12_z index =
          .ok (openings.xor12_z.val[index.val]'(by simpa [openings.xor12_z.property] using
            hindex16)) :=
        index_usize_ok openings.xor12_z index hindex16
      have hq : Canonical (openings.xor12_z.val[index.val]'(by
          simpa [openings.xor12_z.property] using hindex16)) :=
        hopen ⟨index.val, by simpa [openings.xor12_z.property] using
          hindex16⟩
      obtain ⟨q1, hsq, hq1, _hsqv⟩ :=
        AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact
          (openings.xor12_z.val[index.val]'(by simpa [openings.xor12_z.property] using
            hindex16)) hq
      obtain ⟨q2, hsub, _hq2, _hsubv⟩ :=
        AspisR1.EqualityValueAdapter.current_qm_sub_exact q1
          (openings.xor12_z.val[index.val]'(by simpa [openings.xor12_z.property] using
            hindex16)) hq1 hq
      have haddOffsetSpec : (20#usize + index : Result Usize)
          ⦃ dest => dest.val = 20 + index.val ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨dest, hoffset, hdest⟩ := WP.spec_imp_exists haddOffsetSpec
      obtain ⟨range1, hupdate, _hset⟩ := WP.spec_imp_exists
        (Array.update_spec range dest q2 (by simpa [range.property, hdest] using
          (show 20 + index.val < 33 by omega)))
      obtain ⟨index1, hadd, hindex1⟩ := increment_success index hindex
      obtain ⟨outOpen, outRange, hrun, hopenOut⟩ :=
        ih range1 index1 (by omega)
      refine ⟨outOpen, outRange, ?_, hopenOut⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (outOpen, outRange)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hoffset, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range1 index1) =
        .ok (outOpen, outRange)
      rw [hadd, bind_tc_ok]
      exact hrun

/-- The actual sequence of three generated loops succeeds from zero and
preserves the opening record, while deriving the final range canonicality. -/
theorem preprocessing_success_canonical
    (openings : Openings)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z) :
    ∃ openings3 range1 range2 range3,
      Loop0 openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize =
        .ok (openings3, range1) ∧
      Loop1 openings3 range1 0#usize = .ok (openings3, range2) ∧
      Loop2 openings3 range2 0#usize = .ok (openings3, range3) ∧
      openings3 = openings ∧ CanonicalArray range3 := by
  have hzeroIndex : (0#usize).val = 0 := by rfl
  have hspan0 : (0#usize).val + 10 = 10 := by rw [hzeroIndex]
  obtain ⟨openings1, range1, h0, ho1⟩ :=
    loop0_success_fuel 10 openings (Array.repeat 33#usize field.QM31.ZERO)
      0#usize hspan0 hopenZ
  have h0' : Loop0 openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize =
      .ok (openings, range1) := by simpa [ho1] using h0
  obtain ⟨openings2, range2, h1, ho2⟩ :=
    loop1_success_fuel 10 openings range1 0#usize hspan0 hopenSucc
  have h1' : Loop1 openings1 range1 0#usize = .ok (openings2, range2) := by
    simpa [ho1] using h1
  have h1'' : Loop1 openings range1 0#usize = .ok (openings, range2) := by
    simpa [ho2] using h1
  obtain ⟨openings3, range3, h2, ho3⟩ :=
    loop2_success_fuel 10 openings range2 0#usize hspan0 hopenXor
  have h2' : Loop2 openings2 range2 0#usize = .ok (openings3, range3) := by
    simpa [ho2] using h2
  have h2'' : Loop2 openings range2 0#usize = .ok (openings, range3) := by
    simpa [ho3] using h2
  have hzero : CanonicalArray (Array.repeat 33#usize field.QM31.ZERO) :=
    AspisR1.SelectorValueLanePreprocessZeroInit.zero_range_canonical
  have hcanonical : openings3 = openings ∧ CanonicalArray range3 :=
    AspisR1.SelectorValueLanePreprocessCanonical.three_preprocessing_loops_preserve_canonicality
      openings (Array.repeat 33#usize field.QM31.ZERO) openings1 openings2 openings3
      range1 range2 range3 hopenZ hopenSucc hopenXor hzero h0 h1' h2'
  have h0final : Loop0 openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize =
      .ok (openings3, range1) := by simpa [hcanonical.1] using h0'
  have h1final : Loop1 openings3 range1 0#usize = .ok (openings3, range2) := by
    simpa [hcanonical.1] using h1''
  have h2final : Loop2 openings3 range2 0#usize = .ok (openings3, range3) := by
    simpa [hcanonical.1] using h2''
  exact ⟨openings3, range1, range2, range3, h0final, h1final, h2final,
    hcanonical.1, hcanonical.2⟩

#print axioms loop0_success_fuel
#print axioms loop1_success_fuel
#print axioms loop2_success_fuel
#print axioms preprocessing_success_canonical
end AspisR1.SelectorValueLanePreprocessExecution
