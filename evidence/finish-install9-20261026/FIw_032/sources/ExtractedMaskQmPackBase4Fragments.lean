import ExtractedMaskQmPackBase4Tail

/-! Compose the four checked source-coordinate fragments with the actual
reducers and constructor, then compare that factored executable tail with
the generated operation-order tail. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4Fragments

open Aeneas.Std Result
open AspisR1.ExtractedMaskQmPackBase4Arithmetic
open AspisR1.ExtractedMaskQmPackBase4SourceArithmetic
open AspisR1.ExtractedMaskQmPackBase4CheckedU64
open AspisR1.ExtractedMaskQmPackBase4Tail

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def factored (v : Fin 4 → CurrentQM) : Result CurrentQM := do
  let raw00 ← sourceC0a sourceP64
    (UScalar.cast .U64 (v 0).c0.a)
    (UScalar.cast .U64 (v 1).c0.b)
    (UScalar.cast .U64 (v 2).c1.a)
    (UScalar.cast .U64 (v 2).c1.b)
    (UScalar.cast .U64 (v 3).c1.a)
    (UScalar.cast .U64 (v 3).c1.b)
  let raw01 ← sourceC0b sourceP64
    (UScalar.cast .U64 (v 0).c0.b)
    (UScalar.cast .U64 (v 1).c0.a)
    (UScalar.cast .U64 (v 2).c1.a)
    (UScalar.cast .U64 (v 2).c1.b)
    (UScalar.cast .U64 (v 3).c1.a)
    (UScalar.cast .U64 (v 3).c1.b)
  let raw10 ← sourceC1a sourceP64
    (UScalar.cast .U64 (v 0).c1.a)
    (UScalar.cast .U64 (v 1).c1.b)
    (UScalar.cast .U64 (v 2).c0.a)
    (UScalar.cast .U64 (v 3).c0.b)
  let raw11 ← sourceC1b
    (UScalar.cast .U64 (v 0).c1.b)
    (UScalar.cast .U64 (v 1).c1.a)
    (UScalar.cast .U64 (v 2).c0.b)
    (UScalar.cast .U64 (v 3).c0.a)
  let o00 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw00
  let o01 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw01
  let c0 ← AspisR1SelectedMaskProbe.field.CM31.new o00 o01
  let o10 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw10
  let o11 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 raw11
  let c1 ← AspisR1SelectedMaskProbe.field.CM31.new o10 o11
  ok ⟨c0, c1⟩

theorem run_eq_factored (v : Fin 4 → CurrentQM) : run v = factored v := by
  simp [run, factored, packLimbCall, limb_call_exact, sourceP64, sourceC0a, sourceC0b,
    sourceC1a, sourceC1b, AspisR1SelectedMaskProbe.field.CM31.new,
    Aeneas.Std.core.convert.num.FromU64U32.from_val_eq,
    AspisR1.ExtractedMaskReducer.cast_widen_value, bind_tc_ok]

theorem factored_success (v : Fin 4 → CurrentQM)
    (hv : ∀ j, CurrentCanonicalQM (v j)) :
    ∃ out : CurrentQM, factored v = .ok out ∧ CurrentCanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = mathematicalPack v := by
  obtain ⟨raw00, raw01, raw10, raw11,
      h00, hv00, h01, hv01, h10, hv10, h11, hv11⟩ :=
    source_accumulators_qm_limbs v hv
  obtain ⟨o00, ho00, hm00, hc00⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw00
  obtain ⟨o01, ho01, hm01, hc01⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw01
  obtain ⟨o10, ho10, hm10, hc10⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw10
  obtain ⟨o11, ho11, hm11, hc11⟩ :=
    AspisR1.ExtractedMaskReducer.current_wrapper_mod raw11
  let out : CurrentQM := ⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩
  have h00v : o00.val = acc00 v % AspisR1.ExtractedMaskQmPackBase4Arithmetic.P := by rw [← hv00, hm00]
  have h01v : o01.val = acc01 v % AspisR1.ExtractedMaskQmPackBase4Arithmetic.P := by rw [← hv01, hm01]
  have h10v : o10.val = acc10 v % AspisR1.ExtractedMaskQmPackBase4Arithmetic.P := by rw [← hv10, hm10]
  have h11v : o11.val = acc11 v % AspisR1.ExtractedMaskQmPackBase4Arithmetic.P := by rw [← hv11, hm11]
  refine ⟨out, ?_, ?_, ?_⟩
  · simp [factored, h00, h01, h10, h11, ho00, ho01, ho10, ho11,
      AspisR1SelectedMaskProbe.field.CM31.new, bind_tc_ok, out]
  · exact ⟨⟨hc00, hc01⟩, ⟨hc10, hc11⟩⟩
  · simpa [out] using reducedOutput_decode_eq_accumulatorPack v
      o00 o01 o10 o11 h00v h01v h10v h11v |>.trans
        (mathematicalPack_eq_accumulatorPack v hv).symm

theorem run_success (v : Fin 4 → CurrentQM)
    (hv : ∀ j, CurrentCanonicalQM (v j)) :
    ∃ out : CurrentQM, run v = .ok out ∧ CurrentCanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = mathematicalPack v := by
  obtain ⟨out, hout, hcanon, hdecode⟩ := factored_success v hv
  exact ⟨out, run_eq_factored v ▸ hout, hcanon, hdecode⟩

#print axioms run_eq_factored
#print axioms factored_success
#print axioms run_success
end AspisR1.ExtractedMaskQmPackBase4Fragments
