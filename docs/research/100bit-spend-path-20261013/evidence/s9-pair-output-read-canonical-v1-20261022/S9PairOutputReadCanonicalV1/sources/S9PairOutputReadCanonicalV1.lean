import S9PairPublicTopResultV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairOutputReadCanonicalV1

abbrev PairW := Array AspisR1S9PairCallerStepV1.field.WideExact (4#usize)
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CandidateW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev U := Std.Usize
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev ToP6W := AspisR1S9CandidateHelperV1.toP6W
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev cells (a : Array P6W (4#usize)) (j : Fin 4) :=
  AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem index_success_bound {A : Type} {N : Usize}
    (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  have hlen : i.val < a.val.length := by
    by_contra hn
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hn)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa only [a.property] using hlen

private theorem index_value_eq_cells {α : Type} (a : Array α (4#usize))
    (i : U) (x : α) (hi : i.val < 4)
    (hread : Array.index_usize a i = .ok x) :
    AspisR1.S9ArrayWriteScheduleRootV1.cells a ⟨i.val, hi⟩ = x := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨v, hv, hget⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hlen)
  have hvEq : v = x := Result.ok.inj (hv.symm.trans hread)
  have hx : x = v := hvEq.symm
  have hxget : x = a.val[i.val]'(by simpa [a.property] using hi) := hx.trans hget
  exact hxget.symm

/-- Canonicality of any successfully read projected Pair output coefficient,
derived from the same successful Pair public helper call and its mapped-input
canonicality contracts. No output-canonicality premise is assumed. -/
theorem pair_public_output_read_canonical
    (ap0 ap1 : PairW) (extra : Array PairQ (2#usize)) (output : PairW)
    (hpair : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hp0 : ∀ (j : U) (x : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap0)) j = .ok x → Canonical x)
    (hap1 : ∀ (j : U) (x : P6W),
      Array.index_usize (mapArray ToP6W (mapArray PairMapW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9CandidateHelperV1.field.QM31),
      Array.index_usize (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra) j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (idx : U) (coef : AspisR1S9PairCallerStepV1.field.WideExact)
    (hread : Array.index_usize output idx = .ok coef) :
    Canonical (AspisR1S9PairCallerStepV1.toP6W coef) := by
  obtain ⟨q0, q1, hq0, hq1, hcanonical, hcoeff⟩ :=
    AspisR1S9PairPublicTopResultV1.pair_top_success_output_canonical_and_original_coefficients
      ap0 ap1 extra output hpair hp0 hap1 hextra
  have hi : idx.val < 4 := by
    have hb := index_success_bound output idx coef hread
    have hfour : (4#usize).val = 4 := by decide
    omega
  have hmapPair := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    PairMapW output idx
  rw [hread] at hmapPair
  change .ok (PairMapW coef) =
    Array.index_usize (mapArray PairMapW output) idx at hmapPair
  have hreadPairCandidate :
      Array.index_usize (mapArray PairMapW output) idx = .ok (PairMapW coef) := hmapPair.symm
  have hmapP6 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    ToP6W (mapArray PairMapW output) idx
  rw [hreadPairCandidate] at hmapP6
  change .ok (ToP6W (PairMapW coef)) =
    Array.index_usize (mapArray ToP6W (mapArray PairMapW output)) idx at hmapP6
  have hreadP6 :
      Array.index_usize (mapArray ToP6W (mapArray PairMapW output)) idx =
        .ok (ToP6W (PairMapW coef)) := hmapP6.symm
  have hcell := index_value_eq_cells
    (mapArray ToP6W (mapArray PairMapW output)) idx
    (ToP6W (PairMapW coef)) hi hreadP6
  have hc := hcanonical ⟨idx.val, hi⟩
  change Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells
    (mapArray ToP6W (mapArray PairMapW output)) ⟨idx.val, hi⟩) at hc
  rw [hcell] at hc
  change Canonical (AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW coef)) at hc
  rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW] at hc
  exact hc

#print axioms pair_public_output_read_canonical

end AspisR1S9PairOutputReadCanonicalV1
