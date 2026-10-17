import CompositionPartsLoopSlice
import ExtractedMaskHornerPolynomial

/-! Proof adapter for the exact generated candidate loop declarations in
`CompositionPartsLoopSlice`. The declarations themselves are not renamed or
rewritten. -/
set_option autoImplicit false
namespace AspisR1.TerminalCompositionLoopAdapter
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange

abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Prepared := AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor

def coefficient24 (a : Array QM 24#usize) (i : Nat) : ExactQM :=
  if hi : i < 24 then
    AspisR1.ExtractedMaskQM31Exact.decode
      (a.val[i]'(by simpa [a.property] using hi))
  else 0

def coefficient4 (a : Array QM 4#usize) (i : Nat) : ExactQM :=
  if hi : i < 4 then
    AspisR1.ExtractedMaskQM31Exact.decode
      (a.val[i]'(by simpa [a.property] using hi))
  else 0

private theorem loop0_done (semantic : Array QM 24#usize) (prepared : Prepared)
    (iter : ReverseRange) (acc : QM)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
      iter semantic prepared acc = .ok acc := by
  rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0.eq_def]
  simp only [AspisR1.ExtractedMaskReverseRange.reverse_next_done iter hstop,
    bind_tc_ok]

private theorem loop0_step
    (semantic : Array QM 24#usize) (prepared : Prepared)
    (linear acc : QM) (iter : ReverseRange)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
      (24#usize : Usize).val)
    (hlinear : CanonicalQM linear) (hacc : CanonicalQM acc)
    (hprepared : PreparedFor prepared linear)
    (hcoefficient : CanonicalQM
      (semantic.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
        simpa [semantic.property] using hindex))) :
    ∃ acc1 : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        iter semantic prepared acc =
        AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
          ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
          semantic prepared acc1 ∧
      CanonicalQM acc1 ∧
      AspisR1.ExtractedMaskQM31Exact.decode acc1 =
        AspisR1.ExtractedMaskQM31Exact.decode linear *
          AspisR1.ExtractedMaskQM31Exact.decode acc +
          AspisR1.ExtractedMaskQM31Exact.decode
            (semantic.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
              simpa [semantic.property] using hindex)) := by
  let coefficient := semantic.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
    simpa [semantic.property] using hindex)
  have hidx : Array.index_usize semantic
      (Usize.wrapping_sub iter.iter.end 1#usize) = .ok coefficient := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok semantic _ hindex
  obtain ⟨product, hproduct, hproductCanon, hproductValue⟩ :=
    AspisR1.ExtractedMaskPreparedMul.prepared_mul_exact prepared linear acc
      hlinear hacc hprepared
  obtain ⟨acc1, hadd, hacc1, haddValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact product coefficient
      hproductCanon hcoefficient
  refine ⟨acc1, ?_, hacc1, ?_⟩
  · rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0.eq_def]
    simp only [AspisR1.ExtractedMaskReverseRange.reverse_next_step iter hstep,
      bind_tc_ok, hproduct, hidx, hadd, bind_tc_ok]
  · simpa only [AspisR1.ExtractedMaskHornerStep.decode, hproductValue]
      using haddValue

private theorem loop1_done (poseidon : Array QM 4#usize) (prepared : Prepared)
    (iter : ReverseRange) (acc : QM)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
      iter poseidon prepared acc = .ok acc := by
  rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1.eq_def]
  simp only [AspisR1.ExtractedMaskReverseRange.reverse_next_done iter hstop,
    bind_tc_ok]

private theorem loop1_step
    (poseidon : Array QM 4#usize) (prepared : Prepared)
    (linear acc : QM) (iter : ReverseRange)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
      (4#usize : Usize).val)
    (hlinear : CanonicalQM linear) (hacc : CanonicalQM acc)
    (hprepared : PreparedFor prepared linear)
    (hcoefficient : CanonicalQM
      (poseidon.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
        simpa [poseidon.property] using hindex))) :
    ∃ acc1 : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        iter poseidon prepared acc =
        AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
          ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
          poseidon prepared acc1 ∧
      CanonicalQM acc1 ∧
      AspisR1.ExtractedMaskQM31Exact.decode acc1 =
        AspisR1.ExtractedMaskQM31Exact.decode linear *
          AspisR1.ExtractedMaskQM31Exact.decode acc +
          AspisR1.ExtractedMaskQM31Exact.decode
            (poseidon.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
              simpa [poseidon.property] using hindex)) := by
  let coefficient := poseidon.val[(Usize.wrapping_sub iter.iter.end 1#usize).val]'(by
    simpa [poseidon.property] using hindex)
  have hidx : Array.index_usize poseidon
      (Usize.wrapping_sub iter.iter.end 1#usize) = .ok coefficient := by
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok poseidon _ hindex
  obtain ⟨product, hproduct, hproductCanon, hproductValue⟩ :=
    AspisR1.ExtractedMaskPreparedMul.prepared_mul_exact prepared linear acc
      hlinear hacc hprepared
  obtain ⟨acc1, hadd, hacc1, haddValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact product coefficient
      hproductCanon hcoefficient
  refine ⟨acc1, ?_, hacc1, ?_⟩
  · rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1.eq_def]
    simp only [AspisR1.ExtractedMaskReverseRange.reverse_next_step iter hstep,
      bind_tc_ok, hproduct, hidx, hadd, bind_tc_ok]
  · simpa only [AspisR1.ExtractedMaskHornerStep.decode, hproductValue]
      using haddValue

/-- Exact width-24 candidate loop refinement to the shared symbolic Horner
model. The range, canonical-array, prepared-multiplier and initial-accumulator
premises are explicit; no terminal or acceptance conclusion is included. -/
theorem composition_parts_loop0_horner_model
    (semantic : Array QM 24#usize) (prepared : Prepared) (linear acc : QM)
    (iter : ReverseRange) (n : Nat)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n)
    (hn : n ≤ 24) (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear)
    (hcoefficients : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by
        simpa [semantic.property] using
          (show i.val < (24#usize : Usize).val by simpa))))
    (hacc : CanonicalQM acc) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        iter semantic prepared acc = .ok out ∧
      CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.ExtractedMaskHornerLoop.hornerLoopModel
          (coefficient24 semantic)
          (AspisR1.ExtractedMaskQM31Exact.decode linear) n
          (AspisR1.ExtractedMaskQM31Exact.decode acc) := by
  induction n generalizing iter acc with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      refine ⟨acc, loop0_done semantic prepared iter acc hstop, hacc, rfl⟩
  | succ n ih =>
      have hstep : iter.iter.start.val < iter.iter.end.val := by omega
      have hend_pos : 1 ≤ iter.iter.end.val := by omega
      have hindexVal :
          (Usize.wrapping_sub iter.iter.end 1#usize).val = n := by
        rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hend_pos]
        omega
      have hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
          (24#usize : Usize).val := by
        rw [hindexVal]
        have h24 : (24#usize : Usize).val = 24 := by scalar_tac
        rw [h24]
        omega
      let idx := Usize.wrapping_sub iter.iter.end 1#usize
      have hidxVal : idx.val = n := by simpa [idx] using hindexVal
      have hnlt : n < 24 := by omega
      have hidx : idx.val < 24 := by rw [hidxVal]; exact hnlt
      have hcoeffCanon : CanonicalQM
          (semantic.val[idx.val]'(by simpa [semantic.property] using hidx)) := by
        have h := hcoefficients ⟨n, hnlt⟩
        simpa only [hidxVal] using h
      obtain ⟨acc1, hcall, hacc1, hvalue⟩ :=
        loop0_step semantic prepared linear acc iter hstep hindex
          hlinear hacc hprepared hcoeffCanon
      let iter1 : ReverseRange :=
        ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
      have hstart1 : iter1.iter.start.val = 0 := by simpa [iter1] using hstart
      have hend1 : iter1.iter.end.val = n := by
        dsimp [iter1]
        rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hend_pos]
        omega
      obtain ⟨out, hrun, hout, hmodel⟩ :=
        ih acc1 iter1 hstart1 hend1 (by omega) hacc1
      refine ⟨out, ?_, hout, ?_⟩
      · rw [hcall]
        exact hrun
      · have hcoeffEq :
            AspisR1.ExtractedMaskQM31Exact.decode
                (semantic.val[idx.val]'(by simpa [semantic.property] using hidx)) =
              coefficient24 semantic n := by
          simp [coefficient24, hidxVal, hnlt]
        rw [AspisR1.ExtractedMaskHornerLoop.hornerLoopModel, hmodel,
          hvalue, hcoeffEq]

/-- Exact width-4 candidate loop refinement to the same symbolic recurrence. -/
theorem composition_parts_loop1_horner_model
    (poseidon : Array QM 4#usize) (prepared : Prepared) (linear acc : QM)
    (iter : ReverseRange) (n : Nat)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n)
    (hn : n ≤ 4) (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear)
    (hcoefficients : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by
        simpa [poseidon.property] using
          (show i.val < (4#usize : Usize).val by simpa))))
    (hacc : CanonicalQM acc) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        iter poseidon prepared acc = .ok out ∧
      CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.ExtractedMaskHornerLoop.hornerLoopModel
          (coefficient4 poseidon)
          (AspisR1.ExtractedMaskQM31Exact.decode linear) n
          (AspisR1.ExtractedMaskQM31Exact.decode acc) := by
  induction n generalizing iter acc with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      refine ⟨acc, loop1_done poseidon prepared iter acc hstop, hacc, rfl⟩
  | succ n ih =>
      have hstep : iter.iter.start.val < iter.iter.end.val := by omega
      have hend_pos : 1 ≤ iter.iter.end.val := by omega
      have hindexVal :
          (Usize.wrapping_sub iter.iter.end 1#usize).val = n := by
        rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hend_pos]
        omega
      have hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
          (4#usize : Usize).val := by
        rw [hindexVal]
        have h4 : (4#usize : Usize).val = 4 := by scalar_tac
        rw [h4]
        omega
      let idx := Usize.wrapping_sub iter.iter.end 1#usize
      have hidxVal : idx.val = n := by simpa [idx] using hindexVal
      have hnlt : n < 4 := by omega
      have hidx : idx.val < 4 := by rw [hidxVal]; exact hnlt
      have hcoeffCanon : CanonicalQM
          (poseidon.val[idx.val]'(by simpa [poseidon.property] using hidx)) := by
        have h := hcoefficients ⟨n, hnlt⟩
        simpa only [hidxVal] using h
      obtain ⟨acc1, hcall, hacc1, hvalue⟩ :=
        loop1_step poseidon prepared linear acc iter hstep hindex
          hlinear hacc hprepared hcoeffCanon
      let iter1 : ReverseRange :=
        ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
      have hstart1 : iter1.iter.start.val = 0 := by simpa [iter1] using hstart
      have hend1 : iter1.iter.end.val = n := by
        dsimp [iter1]
        rw [AspisR1.ExtractedMaskReverseRange.wrapping_sub_one_val _ hend_pos]
        omega
      obtain ⟨out, hrun, hout, hmodel⟩ :=
        ih acc1 iter1 hstart1 hend1 (by omega) hacc1
      refine ⟨out, ?_, hout, ?_⟩
      · rw [hcall]
        exact hrun
      · have hcoeffEq :
            AspisR1.ExtractedMaskQM31Exact.decode
                (poseidon.val[idx.val]'(by simpa [poseidon.property] using hidx)) =
              coefficient4 poseidon n := by
          simp [coefficient4, hidxVal, hnlt]
        rw [AspisR1.ExtractedMaskHornerLoop.hornerLoopModel, hmodel,
          hvalue, hcoeffEq]

#print axioms composition_parts_loop0_horner_model
#print axioms composition_parts_loop1_horner_model
end AspisR1.TerminalCompositionLoopAdapter
