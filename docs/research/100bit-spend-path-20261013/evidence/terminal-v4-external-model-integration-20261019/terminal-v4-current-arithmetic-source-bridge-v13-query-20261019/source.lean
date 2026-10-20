import TerminalV4CurrentArithmeticInstantiationV1
import TerminalV4EqualityValueResultRefinementV7
import TerminalV4EqualityValueResultRefinementV3
import TerminalV4TerminalPartsArithmeticJoinChunk13V2
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridgeV12

open AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract

abbrev QM := field.QM31

theorem result_bind_assoc {α β γ : Type} (r : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (r >>= f) >>= g = r >>= fun x => f x >>= g := by
  cases r <;> rfl

/-- Instantiated exact arithmetic for the current caller: only canonicality of
its five supplied operands and exactness of equality_value remain explicit. -/
theorem terminal_parts_success_of_caller_and_exact_value
    (compositionCaller : TerminalPartsCompositionCaller)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize)
    (point zerocheck_point : Array QM 10#usize)
    (lambda chi theta mu composition h1Z copyActive : QM)
    (c1 : Array QM 16#usize)
    (mask_only : Array QM 10#usize)
    (g : QM)
    (hcaller : compositionCaller public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask_only, g, h1Z, copyActive)))
    (hzero : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        (zerocheck_point.val[i.val]'(by simpa [zerocheck_point.property] using i.isLt)))
    (hpoint : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        (point.val[i.val]'(by simpa [point.property] using i.isLt)))
    (hc : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM composition)
    (hh : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM h1Z)
    (ha : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM copyActive)
    (hm : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM mu) :
    ∃ out, pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      compositionCaller public1 claims point lambda chi theta zerocheck_point mu =
        .ok (core.result.Result.Ok (out, c1, mask_only, g)) ∧
      AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM out ∧
      AspisR1.TerminalV4QM31Exact.decode out =
        (AspisR1.TerminalV4EqualityValueResultRefinement.expectedEquality
          zerocheck_point point *
          AspisR1.TerminalV4QM31Exact.decode composition +
          AspisR1.TerminalV4QM31Exact.decode mu *
          AspisR1.TerminalV4QM31Exact.decode h1Z) +
        (AspisR1.TerminalV4QM31Exact.decode mu *
          AspisR1.TerminalV4QM31Exact.decode mu) *
          ((1 - AspisR1.TerminalV4QM31Exact.decode copyActive) *
            AspisR1.TerminalV4QM31Exact.decode h1Z) := by
  obtain ⟨q, heq, hq, hqvalue⟩ :=
    AspisR1.TerminalV4EqualityValueResultRefinement.equality_value_exists_canonical_and_exact
      zerocheck_point point hzero hpoint
  unfold AspisR1.TerminalV4EqualityValueResultRefinement.HasExpectedEquality at hqvalue
  obtain ⟨out, hrun, hcanon, hdecode⟩ :=
    AspisR1.TerminalV4CurrentArithmeticInstantiation.run_exact
      q composition h1Z copyActive mu hq hc hh ha hm
  refine ⟨out, ?_, hcanon, ?_⟩
  · rw [AspisR1SelectedMaskProbe.terminal_parts_caller_to_arithmetic_tail
      compositionCaller public1 claims point zerocheck_point lambda chi theta mu
      composition h1Z copyActive c1 mask_only g hcaller]
    rw [heq]
    simp only [bind_tc_ok]
    have hmapped := congrArg
      (fun r : Result QM => r >>= fun out =>
        Result.ok (core.result.Result.Ok
          (out, c1, mask_only, g) : core.result.Result
            (QM × (Array QM 16#usize) × (Array QM 10#usize) × QM)
            pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)) hrun
    simpa only [AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run,
      result_bind_assoc, bind_tc_ok] using hmapped
  · rw [hqvalue] at hdecode
    simpa [AspisR1.TerminalV4CurrentArithmeticInstantiation.laws,
      AspisR1.TerminalV4Constants.one_decode] using hdecode

#print axioms terminal_parts_success_of_caller_and_exact_value

end AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridgeV12
