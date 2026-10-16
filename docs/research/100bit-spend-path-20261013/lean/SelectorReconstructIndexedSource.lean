import SelectorValueLaneIndexedSlice
import SelectorReconstructIndexedCanonical
import SelectorReconstructIndexModel
import SelectorExpansionCorrectness
import ExtractedMaskQM31Exact
import ExtractedMaskReducerOps

/-! Source-to-model proof for the v3 explicit descending-index reconstruction
loop. The theorem consumes the actual generated loop/wrapper and proves its
canonical output and exact `valueReconstruct10` value on canonical cells. -/
set_option autoImplicit false
namespace AspisR1.SelectorReconstructIndexedSource

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.SelectorReconstructIndexedCanonical
open AspisR1.SelectorReconstructIndexModel

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

private def cellAt (view : Array QM 16#usize) (i : Nat) : QM :=
  if h : i < 16 then view.val[i]'(by simpa [view.property] using h)
  else field.QM31.ZERO

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem sub_one_success (i : Usize) (hi : 0 < i.val) :
    ∃ i1 : Usize, UScalar.sub i 1#usize = .ok i1 ∧ i1.val = i.val - 1 := by
  have hle : (1#usize).val ≤ i.val := by
    norm_num
    omega
  obtain ⟨i1, hrun, hval⟩ := sub_success i 1#usize hle
  exact ⟨i1, hrun, by simpa using hval⟩

/-- The generated loop at index `n` always succeeds on canonical inputs and
refines the checked symbolic recurrence. -/
theorem reconstruct_10_loop_success
    (view : Array QM 16#usize) (n : Nat) (i : Usize) (acc : QM)
    (hi : i.val = n) (hn : n ≤ 9)
    (hacc : Canonical acc)
    (hview : ∀ j, j ≤ 9 → Canonical (cellAt view j)) :
    ∃ out, AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop
      view acc i = .ok out ∧ Canonical out ∧ decode out =
        AspisR1.SelectorReconstructIndexModel.reconstructIndexed
          (fun j => decode (cellAt view j)) n (decode acc) := by
  induction n using Nat.strong_induction_on generalizing i acc with
  | h n ih =>
      by_cases hpositive : 0 < n
      · have hgt : i > 0#usize := by
          change (0#usize : Usize) < i
          rw [UScalar.lt_equiv]
          simpa [hi] using hpositive
        obtain ⟨i1, hsub, hsubVal⟩ := sub_one_success i (by simpa [hi] using hpositive)
        have hreadBound : i1.val < 16 := by omega
        have hread : Array.index_usize view i1 =
            .ok (view.val[i1.val]'(by simpa [view.property] using hreadBound)) :=
          index_usize_ok view i1 hreadBound
        let q := cellAt view i1.val
        have hqEq : q = view.val[i1.val]'(by simpa [view.property] using hreadBound) := by
          simp [q, cellAt, hreadBound]
        have hreadQ : Array.index_usize view i1 = .ok q := by
          rw [hread, ← hqEq]
        have hq : Canonical q := by
          simpa [q] using hview i1.val (by omega)
        obtain ⟨double, hdoubleRun, hdoubleCan, hdoubleDec⟩ :=
          current_qm_add_exact acc acc hacc hacc
        obtain ⟨sum, hsumRun, hsumCan, hsumDec⟩ :=
          current_qm_add_exact double q hdoubleCan hq
        have hn1 : n - 1 < n := by omega
        have hi1 : i1.val = n - 1 := by omega
        obtain ⟨out, hrun, hcanon, hdecode⟩ :=
          ih (n - 1) hn1 i1 sum hi1 (by omega) hsumCan
        refine ⟨out, ?_, hcanon, ?_⟩
        · rw [AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop.eq_def]
          simp only [if_pos hgt]
          change (do
            let i1 ← UScalar.sub i 1#usize
            let q ← field.QM31.add acc acc
            let q1 ← view.index_usize i1
            let acc1 ← field.QM31.add q q1
            AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop
              view acc1 i1) = .ok out
          have hreadQ' : view.index_usize i1 = .ok q := by
            change Array.index_usize view i1 = .ok q
            exact hreadQ
          simp only [hsub, bind_tc_ok, hdoubleRun, bind_tc_ok,
            hreadQ', bind_tc_ok, hsumRun, bind_tc_ok]
          exact hrun
        · calc
            decode out = reconstructIndexed (fun j => decode (cellAt view j)) (n - 1) (decode sum) := hdecode
            _ = reconstructIndexed (fun j => decode (cellAt view j)) ((n - 1) + 1)
                  (decode acc) := by
                  rw [hsumDec, hdoubleDec]
                  have hqDecode : decode q = decode (cellAt view (n - 1)) := by
                    have hcell : n - 1 < 16 := by omega
                    simp [q, hi1, cellAt, hcell]
                  rw [hqDecode]
                  rfl
            _ = reconstructIndexed (fun j => decode (cellAt view j)) n (decode acc) := by
                  have hidx : (n - 1) + 1 = n := by omega
                  rw [hidx]
      · have hn0 : n = 0 := by omega
        have hnot : ¬ i > 0#usize := by
          change ¬ (0#usize : Usize) < i
          rw [UScalar.lt_equiv]
          simp [hi, hn0]
        refine ⟨acc, ?_, hacc, ?_⟩
        · rw [AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop.eq_def]
          simp only [if_neg hnot]
        · simp [AspisR1.SelectorReconstructIndexModel.reconstructIndexed, hn0]

/-- The generated wrapper reads cell 9 and invokes the generated loop at 9;
this yields the retained ten-cell value reconstruction theorem. -/
theorem reconstruct_10_success
    (view : Array QM 16#usize)
    (hcanonical : AspisR1.SelectorExpansionCorrectness.canonicalArray view) :
    ∃ out, AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10
      view = .ok out ∧ Canonical out ∧ decode out =
      R0P.valueReconstruct10
        (fun i : Fin 16 => decode (view.val[i.val]'(by
          simpa [view.property] using i.isLt))) := by
  have hread := index_usize_ok view 9#usize (by decide)
  have hacc : Canonical (view.val[9]'(by simpa [view.property] using show 9 < 16 by decide)) :=
    hcanonical ⟨9, by simpa [view.property] using (show 9 < 16 by decide)⟩
  have hview : ∀ j, j ≤ 9 → Canonical (cellAt view j) := by
    intro j hj
    have hj16 : j < 16 := by omega
    have hcell := hcanonical ⟨j, by simpa [view.property] using hj16⟩
    simpa [cellAt, hj16] using hcell
  obtain ⟨out, hrun, houtCanonical, hdecode⟩ :=
    reconstruct_10_loop_success view 9 9#usize
      (view.val[9]'(by simpa [view.property] using show 9 < 16 by decide)) rfl
      (by omega) hacc hview
  refine ⟨out, ?_, houtCanonical, ?_⟩
  · rw [AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.reconstruct_10]
    simp only [hread, bind_tc_ok]
    exact hrun
  · calc
      decode out = reconstructIndexed (fun j => decode (cellAt view j)) 9
          (decode (view.val[9]'(by simpa [view.property] using show 9 < 16 by decide))) := hdecode
      _ = R0P.valueReconstruct10
          (fun i : Fin 16 => decode (view.val[i.val]'(by
            simpa [view.property] using i.isLt))) := by
            simpa [cellAt] using reconstructIndexed_nine_eq_valueReconstruct10
              (fun i : Nat => decode (cellAt view i))

#print axioms reconstruct_10_loop_success
#print axioms reconstruct_10_success
end AspisR1.SelectorReconstructIndexedSource
