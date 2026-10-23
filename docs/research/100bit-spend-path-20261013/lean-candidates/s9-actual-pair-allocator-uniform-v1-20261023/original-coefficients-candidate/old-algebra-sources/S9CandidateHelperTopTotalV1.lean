import S9CandidateHelperTwoBodyTotalV1
import S9CandidateOriginalCoefficientsBridgeV4
import S9CandidateOutputCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateHelperTopTotalV1

open AspisR1S9CandidateHelperV1

abbrev U := Std.Usize
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PArray := Array PW (4#usize)
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev TraceDecode := AspisR1S9CandidateOriginalCoefficientsBridgeV4.TraceDecode
abbrev ScaledBase := AspisR1S9CandidateOriginalCoefficientsBridgeV4.ScaledBase
abbrev Seed := AspisR1S9CandidateOriginalCoefficientsBridgeV4.Seed
abbrev cells (a : PArray) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem generated_to_current_q (x : AspisR1S9HelperP6.field.QM31) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

/-- The actual zero-initialized candidate wrapper is total under canonical
input reads; its mapped result has all four canonical cells and satisfies the
original two-seed S2 coefficient equations. -/
theorem candidate_helper_top_total
    (ap0 ap1 : Array CW (4#usize)) (extra : Array CQ (2#usize))
    (hp0 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x)) :
    ∃ output q0 q1,
      AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
        ap0 ap1 extra = .ok output ∧
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4, Canonical (cells (mapArray AspisR1S9CandidateHelperV1.toP6W output) j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells (mapArray AspisR1S9CandidateHelperV1.toP6W output) j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase (mapArray AspisR1S9CandidateHelperV1.toP6W ap0))
            (ScaledBase (mapArray AspisR1S9CandidateHelperV1.toP6W ap1))
            (Seed (AspisR1S9CandidateHelperV1.toP6Q q0))
            (Seed (AspisR1S9CandidateHelperV1.toP6Q q1)) j) := by
  have hextraMapped : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x) := by
    intro j x hx
    obtain ⟨xc, hxc, hmap⟩ :=
      AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
        AspisR1S9CandidateHelperV1.toP6Q extra j x hx
    have hc := hextra j xc hxc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM
        (AspisR1S9CandidateHelperV1.toP6Q xc)) at hc
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)
    rw [← hmap, ← generated_to_current_q]
    exact hc
  let initial : Array CW (4#usize) :=
    Array.repeat 4#usize AspisR1S9CandidateHelperV1.field.WideExact.ZERO
  obtain ⟨output, hloop⟩ :=
    AspisR1S9CandidateHelperTwoBodyTotalV1.candidate_helper_total
      ap0 ap1 extra initial hp0 hap1 hextraMapped
  have htop : AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output := by
    unfold AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
    change _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      { start := 0#usize, «end» := 2#usize } ap0 ap1 extra initial = .ok output
    simpa only [AspisR1S9CandidateTwoBodyCallsV1.start0] using hloop
  obtain ⟨q0,q1,hq0,hq1,hcoeff⟩ :=
    AspisR1S9CandidateOriginalCoefficientsBridgeV4.candidate_top_success_has_original_coefficients
      ap0 ap1 extra output htop hp0 hap1 hextra
  have hcanonical :=
    AspisR1S9CandidateOutputCanonicalV1.candidate_top_success_output_all_canonical
      ap0 ap1 extra output htop hp0 hap1 hextra
  exact ⟨output,q0,q1,htop,hq0,hq1,hcanonical,hcoeff⟩

#print axioms candidate_helper_top_total

end AspisR1S9CandidateHelperTopTotalV1
