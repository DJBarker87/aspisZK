import S9PairSameLowCanonicalV1
import S9PairSideOneFullArrayCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideOneBodyFullArrayCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev U := Std.Usize
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev PairArray := Array PW 4#usize
abbrev PairQArray := Array PQ 2#usize
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev P6Q := AspisR1S9HelperP6.field.QM31
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev PairMapQ := AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ
abbrev P6MapW := AspisR1S9CandidateHelperV1.toP6W
abbrev P6MapQ := AspisR1S9CandidateHelperV1.toP6Q
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- The side-one actual active body produces a fully canonical mapped output
array. Its scalar low is derived from the same successful body through the
existing candidate-prefix bridge, and the three side-one writes are handled
by the same-run after-low consumer. -/
theorem side_one_active_body_output_array_canonical
    (ap0 ap1 : PairArray) (extra : PairQArray)
    (iterNext : PR) (weights : PairArray)
    (flow : ControlFlow (PR × PairArray) PairArray)
    (hbody : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
      ap0 ap1 extra 1#usize iterNext weights = .ok flow)
    (hap0 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap0)) j = .ok v →
      Canonical v)
    (hap1 : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v)
    (hextra : ∀ (j : U) (v : P6Q),
      Array.index_usize (mapArray P6MapQ (mapArray PairMapQ extra)) j = .ok v →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM v))
    (hweights : ∀ (j : U) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW weights)) j = .ok v →
      Canonical v) :
    ∃ (output : PairArray),
      flow = .cont (iterNext, output) ∧
      (∀ (j : U) (v : P6W),
        Array.index_usize (mapArray P6MapW (mapArray PairMapW output)) j = .ok v →
        Canonical v) := by
  obtain ⟨q, q1, q2, q3, unusedQ4, q4, q41, q8, q12, q16, low,
      _hq, _hq1, _hq2, _hq3, _hunusedQ4, _hq4, _hq41, _hq8, _hq12,
      _hq16, _hlowCall, hafter, hlowCan⟩ :=
    AspisR1S9PairSameLowCanonicalV1.same_pair_body_low_is_canonical
      ap0 ap1 extra 1#usize iterNext weights flow hbody (by decide)
      hap0 hap1 hextra
  exact AspisR1S9PairSideOneFullArrayCanonicalV1.side_one_after_low_full_array_canonical
    ap1 iterNext weights q41 q8 q12 q16 low flow hafter hap1 hweights hlowCan

#print axioms side_one_active_body_output_array_canonical

end AspisR1S9PairSideOneBodyFullArrayCanonicalV1
