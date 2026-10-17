import CopyResidualSource

/-! Source refinement of the actual Copy rational residual, reusing the
checked QM31 arithmetic lemmas. No source arithmetic success is an input. -/
set_option autoImplicit false
namespace AspisR1.CopyResidualExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Row := AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.CopyRowExtension
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def cell (xs : Array QM 2#usize) (i : Fin 2) : QM :=
  xs.val[i.val]'(by simpa [xs.property] using i.isLt)

def modelRow (row : Row) : R0P.CopyRowExtension ExactQM :=
  ⟨fun i => decode (cell row.producer_values i),
   fun i => decode (cell row.producer_weights i),
   fun i => decode (cell row.consumer_values i),
   fun i => decode (cell row.consumer_weights i)⟩
private theorem read_two_0 (xs : Array QM 2#usize) :
    Array.index_usize xs 0#usize = .ok (cell xs 0) := by
  simpa [cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    xs 0#usize (by norm_num)
private theorem read_two_1 (xs : Array QM 2#usize) :
    Array.index_usize xs 1#usize = .ok (cell xs 1) := by
  simpa [cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    xs 1#usize (by norm_num)
private theorem read_four_0 (a b c d : QM) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := by
  simpa [Array.make] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array.make 4#usize [a,b,c,d]) 0#usize (by norm_num)
private theorem read_four_1 (a b c d : QM) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := by
  simpa [Array.make] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array.make 4#usize [a,b,c,d]) 1#usize (by norm_num)
private theorem read_four_2 (a b c d : QM) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := by
  simpa [Array.make] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array.make 4#usize [a,b,c,d]) 2#usize (by norm_num)
private theorem read_four_3 (a b c d : QM) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := by
  simpa [Array.make] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array.make 4#usize [a,b,c,d]) 3#usize (by norm_num)
/-- Canonical row cells, helper and challenge suffice for actual source
success and the exact retained Copy residual polynomial. Pattern/link and
active-mask production remain enclosing-caller obligations. -/
theorem copy_residual_exact (row : Row) (helper chi : QM)
    (hpv : ∀ i : Fin 2, CanonicalQM (cell row.producer_values i))
    (hpw : ∀ i : Fin 2, CanonicalQM (cell row.producer_weights i))
    (hcv : ∀ i : Fin 2, CanonicalQM (cell row.consumer_values i))
    (hcw : ∀ i : Fin 2, CanonicalQM (cell row.consumer_weights i))
    (hhelper : CanonicalQM helper) (hchi : CanonicalQM chi) :
    ∃ out,
      AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual
        row helper chi = .ok out ∧ CanonicalQM out ∧
      decode out = R0P.copyResidual (modelRow row) (decode helper) (decode chi) := by
  let p0 := cell row.producer_values 0
  have hcp0 : CanonicalQM p0 := hpv 0
  let p1 := cell row.producer_values 1
  have hcp1 : CanonicalQM p1 := hpv 1
  let c0 := cell row.consumer_values 0
  have hcc0 : CanonicalQM c0 := hcv 0
  let c1 := cell row.consumer_values 1
  have hcc1 : CanonicalQM c1 := hcv 1
  let pw0 := cell row.producer_weights 0
  have hcpw0 : CanonicalQM pw0 := hpw 0
  let pw1 := cell row.producer_weights 1
  have hcpw1 : CanonicalQM pw1 := hpw 1
  let cw0 := cell row.consumer_weights 0
  have hccw0 : CanonicalQM cw0 := hcw 0
  let cw1 := cell row.consumer_weights 1
  have hccw1 : CanonicalQM cw1 := hcw 1
  obtain ⟨q1, hq1, hcq1, hvq1⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact chi p0 hchi hcp0
  change decode q1 = decode chi - decode p0 at hvq1
  obtain ⟨q3, hq3, hcq3, hvq3⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact chi p1 hchi hcp1
  change decode q3 = decode chi - decode p1 at hvq3
  obtain ⟨q5, hq5, hcq5, hvq5⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact chi c0 hchi hcc0
  change decode q5 = decode chi - decode c0 at hvq5
  obtain ⟨q7, hq7, hcq7, hvq7⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact chi c1 hchi hcc1
  change decode q7 = decode chi - decode c1 at hvq7
  obtain ⟨producer_denominator, hproducer_denominator, hcproducer_denominator, hvproducer_denominator⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q1 q3 hcq1 hcq3
  change decode producer_denominator = decode q1 * decode q3 at hvproducer_denominator
  obtain ⟨consumer_denominator, hconsumer_denominator, hcconsumer_denominator, hvconsumer_denominator⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact q5 q7 hcq5 hcq7
  change decode consumer_denominator = decode q5 * decode q7 at hvconsumer_denominator
  obtain ⟨q13, hq13, hcq13, hvq13⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact pw0 q3 hcpw0 hcq3
  change decode q13 = decode pw0 * decode q3 at hvq13
  obtain ⟨q15, hq15, hcq15, hvq15⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact pw1 q1 hcpw1 hcq1
  change decode q15 = decode pw1 * decode q1 at hvq15
  obtain ⟨producer_numerator, hproducer_numerator, hcproducer_numerator, hvproducer_numerator⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q13 q15 hcq13 hcq15
  change decode producer_numerator = decode q13 + decode q15 at hvproducer_numerator
  obtain ⟨q17, hq17, hcq17, hvq17⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact cw0 q7 hccw0 hcq7
  change decode q17 = decode cw0 * decode q7 at hvq17
  obtain ⟨q19, hq19, hcq19, hvq19⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact cw1 q5 hccw1 hcq5
  change decode q19 = decode cw1 * decode q5 at hvq19
  obtain ⟨consumer_numerator, hconsumer_numerator, hcconsumer_numerator, hvconsumer_numerator⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q17 q19 hcq17 hcq19
  change decode consumer_numerator = decode q17 + decode q19 at hvconsumer_numerator
  obtain ⟨q20, hq20, hcq20, hvq20⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact helper consumer_denominator hhelper hcconsumer_denominator
  change decode q20 = decode helper * decode consumer_denominator at hvq20
  obtain ⟨q21, hq21, hcq21, hvq21⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact q20 consumer_numerator hcq20 hcconsumer_numerator
  change decode q21 = decode q20 + decode consumer_numerator at hvq21
  obtain ⟨q22, hq22, hcq22, hvq22⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact producer_denominator q21 hcproducer_denominator hcq21
  change decode q22 = decode producer_denominator * decode q21 at hvq22
  obtain ⟨q23, hq23, hcq23, hvq23⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact consumer_denominator producer_numerator hcconsumer_denominator hcproducer_numerator
  change decode q23 = decode consumer_denominator * decode producer_numerator at hvq23
  obtain ⟨out, hout, hcout, hvout⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact q22 q23 hcq22 hcq23
  change decode out = decode q22 - decode q23 at hvout
  refine ⟨out, ?_, hcout, ?_⟩
  · simp only [AspisR1CopyResidualCandidate.pool_v1.pair_forest_copy_terminal.copy_residual,
      read_two_0, read_two_1, read_four_0, read_four_1, read_four_2, read_four_3, p0, p1, c0, c1, pw0, pw1, cw0, cw1, hq1, hq3, hq5, hq7, hproducer_denominator, hconsumer_denominator, hq13, hq15, hproducer_numerator, hq17, hq19, hconsumer_numerator, hq20, hq21, hq22, hq23, hout, bind_tc_ok]
  · change decode out =
      (decode chi - decode p0) * (decode chi - decode p1) *
        (decode helper * ((decode chi - decode c0) * (decode chi - decode c1)) +
          (decode cw0 * (decode chi - decode c1) + decode cw1 * (decode chi - decode c0))) -
      ((decode chi - decode c0) * (decode chi - decode c1)) *
        (decode pw0 * (decode chi - decode p1) + decode pw1 * (decode chi - decode p0))
    rw [hvout, hvq23, hvq22, hvq21, hvq20, hvconsumer_numerator, hvq19, hvq17, hvproducer_numerator, hvq15, hvq13, hvconsumer_denominator, hvproducer_denominator, hvq7, hvq5, hvq3, hvq1]

#print axioms copy_residual_exact
end
end AspisR1.CopyResidualExact
