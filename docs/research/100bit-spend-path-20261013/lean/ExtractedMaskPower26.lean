import ExtractedMaskQM31SquareExact
import ExtractedMaskQM31Exact

/-! Operation-level correctness of the extracted `mask_power_26` call chain.
The proof composes checked square/multiply contracts and symbolic exponent
arithmetic; it does not unfold field recurrences. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskPower26

open Aeneas.Std Result

abbrev QM := AspisR1.ExtractedMaskQM31SquareExact.QM
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31SquareExact.CanonicalQM
abbrev Exact := AspisR1.ExtractedMaskQM31SquareExact.Exact

def decode (x : QM) : Exact := AspisR1.ExtractedMaskQM31SquareExact.decode x

theorem current_mask_power_26 (value : QM)
    (hvalue : CanonicalQM value) :
    ∃ result : QM,
      AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26 value = .ok result ∧
      CanonicalQM result ∧ decode result = decode value ^ 26 := by
  obtain ⟨x2, hx2, hcan2, hd2⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact value hvalue
  obtain ⟨x4, hx4, hcan4, hd4⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact x2 hcan2
  obtain ⟨x8, hx8, hcan8, hd8⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact x4 hcan4
  obtain ⟨x16, hx16, hcan16, hd16⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact x8 hcan8
  obtain ⟨x24, hx24, hcan24, hd24⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact x16 x8 hcan16 hcan8
  obtain ⟨result, hresult, hcanResult, hdResult⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact x24 x2 hcan24 hcan2
  have hp2 : AspisR1.ExtractedMaskQM31Exact.decode x2 =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 2 := by
    simpa [AspisR1.ExtractedMaskQM31SquareExact.decode,
      AspisR1.ExtractedMaskQM31Exact.decode, pow_two] using hd2
  have hp4 : AspisR1.ExtractedMaskQM31Exact.decode x4 =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 4 := by
    have hd4' : AspisR1.ExtractedMaskQM31Exact.decode x4 =
        AspisR1.ExtractedMaskQM31Exact.decode x2 *
          AspisR1.ExtractedMaskQM31Exact.decode x2 := by
      simpa [AspisR1.ExtractedMaskQM31SquareExact.decode,
        AspisR1.ExtractedMaskQM31Exact.decode] using hd4
    rw [hd4', hp2, ← pow_add]
  have hp8 : AspisR1.ExtractedMaskQM31Exact.decode x8 =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 8 := by
    have hd8' : AspisR1.ExtractedMaskQM31Exact.decode x8 =
        AspisR1.ExtractedMaskQM31Exact.decode x4 *
          AspisR1.ExtractedMaskQM31Exact.decode x4 := by
      simpa [AspisR1.ExtractedMaskQM31SquareExact.decode,
        AspisR1.ExtractedMaskQM31Exact.decode] using hd8
    rw [hd8', hp4, ← pow_add]
  have hp16 : AspisR1.ExtractedMaskQM31Exact.decode x16 =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 16 := by
    have hd16' : AspisR1.ExtractedMaskQM31Exact.decode x16 =
        AspisR1.ExtractedMaskQM31Exact.decode x8 *
          AspisR1.ExtractedMaskQM31Exact.decode x8 := by
      simpa [AspisR1.ExtractedMaskQM31SquareExact.decode,
        AspisR1.ExtractedMaskQM31Exact.decode] using hd16
    rw [hd16', hp8, ← pow_add]
  have hp24 : AspisR1.ExtractedMaskQM31Exact.decode x24 =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 24 := by
    have hd24' : AspisR1.ExtractedMaskQM31Exact.decode x24 =
        AspisR1.ExtractedMaskQM31Exact.decode x16 *
          AspisR1.ExtractedMaskQM31Exact.decode x8 := by
      simpa [AspisR1.ExtractedMaskQM31Exact.decode] using hd24
    rw [hd24', hp16, hp8, ← pow_add]
  refine ⟨result, ?_, hcanResult, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26,
      hx2, hx4, hx8, hx16, hx24, hresult, bind_tc_ok]
  · change AspisR1.ExtractedMaskQM31Exact.decode result =
      AspisR1.ExtractedMaskQM31Exact.decode value ^ 26
    calc
      AspisR1.ExtractedMaskQM31Exact.decode result =
          AspisR1.ExtractedMaskQM31Exact.decode x24 *
            AspisR1.ExtractedMaskQM31Exact.decode x2 := by
        simpa [AspisR1.ExtractedMaskQM31SquareExact.decode,
          AspisR1.ExtractedMaskQM31Exact.decode] using hdResult
      _ = AspisR1.ExtractedMaskQM31Exact.decode value ^ 24 *
          AspisR1.ExtractedMaskQM31Exact.decode value ^ 2 := by
        rw [hp24, hp2]
      _ = AspisR1.ExtractedMaskQM31Exact.decode value ^ 26 := by
        rw [← pow_add]

#print axioms current_mask_power_26

end AspisR1.ExtractedMaskPower26
