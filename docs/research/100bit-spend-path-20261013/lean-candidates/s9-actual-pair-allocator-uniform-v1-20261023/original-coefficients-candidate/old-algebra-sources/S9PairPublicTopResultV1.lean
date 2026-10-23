import S9PairTopWrapperMapV1
import S9CandidateHelperTopTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairPublicTopResultV1

abbrev PairW := Array AspisR1S9PairCallerStepV1.field.WideExact (4#usize)
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PairArray := PairW
abbrev CandidateW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev CandidateQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev P6Q := AspisR1S9HelperP6.field.QM31
abbrev U := Std.Usize
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev PairMapQ := AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
abbrev ToP6W := AspisR1S9CandidateHelperV1.toP6W
abbrev ToP6Q := AspisR1S9CandidateHelperV1.toP6Q
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev TraceDecode := AspisR1S9CandidateOriginalCoefficientsBridgeV4.TraceDecode
abbrev ScaledBase := AspisR1S9CandidateOriginalCoefficientsBridgeV4.ScaledBase
abbrev Seed := AspisR1S9CandidateOriginalCoefficientsBridgeV4.Seed
abbrev cells (a : Array P6W (4#usize)) (j : Fin 4) :=
  AspisR1.S9ArrayWriteScheduleRootV1.cells a j

/-- The selected Pair public helper wrapper inherits the Candidate top theorem:
its successful result has four canonical returned cells and the original S2
coefficient equations. Canonical input-read obligations are stated on the
selected mapped P6 arrays, matching the Candidate theorem's contract. -/
theorem pair_top_success_output_canonical_and_original_coefficients
    (ap0 ap1 : PairArray) (extra : Array PairQ (2#usize)) (output : PairArray)
    (hpair : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hp0 : ∀ (j : U) (x : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap0)) j = .ok x → Canonical x)
    (hap1 : ∀ (j : U) (x : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : CandidateQ),
      Array.index_usize (mapArray PairMapQ extra) j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6 (ToP6Q x)) :
    ∃ q0 q1 : PairQ,
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4,
        Canonical (cells (mapArray ToP6W (mapArray PairMapW output)) j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells (mapArray ToP6W (mapArray PairMapW output)) j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase (mapArray ToP6W (mapArray PairMapW ap0)))
            (ScaledBase (mapArray ToP6W (mapArray PairMapW ap1)))
            (Seed (ToP6Q (PairMapQ q0)))
            (Seed (ToP6Q (PairMapQ q1))) j) := by
  have hpairMap := AspisR1S9PairTopWrapperMapV1.pair_top_success_maps_to_candidate
    ap0 ap1 extra output hpair
  obtain ⟨candidateOutput, q0c, q1c, hcandidate, hq0c, hq1c,
      hcanonical, hcoeff⟩ :=
    AspisR1S9CandidateHelperTopTotalV1.candidate_helper_top_total
      (mapArray PairMapW ap0) (mapArray PairMapW ap1) (mapArray PairMapQ extra)
      hp0 hap1 hextra
  have houtput : candidateOutput = mapArray PairMapW output :=
    Result.ok.inj (hcandidate.symm.trans hpairMap)
  subst candidateOutput
  obtain ⟨q0, hq0, hq0map⟩ :=
    AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      PairMapQ extra 0#usize q0c hq0c
  obtain ⟨q1, hq1, hq1map⟩ :=
    AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      PairMapQ extra 1#usize q1c hq1c
  refine ⟨q0, q1, hq0, hq1, hcanonical, ?_⟩
  intro j
  rw [← hq0map, ← hq1map] at hcoeff
  exact hcoeff j

#print axioms pair_top_success_output_canonical_and_original_coefficients

end AspisR1S9PairPublicTopResultV1
