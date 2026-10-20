import TerminalV4CurrentArithmeticInstantiationV1
import TerminalV4TerminalPartsArithmeticJoinChunk13V2
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridgeV6

open AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract

abbrev QM := field.QM31

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
    (g q : QM)
    (hcaller : compositionCaller public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask_only, g, h1Z, copyActive)))
    (heq : pool_v1.pair_forest_semantic_terminal.equality_value
      zerocheck_point point = .ok q)
    (hq : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM q)
    (hc : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM composition)
    (hh : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM h1Z)
    (ha : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM copyActive)
    (hm : AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM mu) :
    ∃ out, pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      compositionCaller public1 claims point lambda chi theta zerocheck_point mu =
        .ok (core.result.Result.Ok (out, c1, mask_only, g)) ∧
      AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM out ∧
      AspisR1.TerminalV4QM31Exact.decode out =
        (AspisR1.TerminalV4QM31Exact.decode q *
          AspisR1.TerminalV4QM31Exact.decode composition +
          AspisR1.TerminalV4QM31Exact.decode mu *
          AspisR1.TerminalV4QM31Exact.decode h1Z) +
        (AspisR1.TerminalV4QM31Exact.decode mu *
          AspisR1.TerminalV4QM31Exact.decode mu) *
          ((1 - AspisR1.TerminalV4QM31Exact.decode copyActive) *
            AspisR1.TerminalV4QM31Exact.decode h1Z) := by
  obtain ⟨out, hrun, hcanon, hdecode⟩ :=
    AspisR1.TerminalV4CurrentArithmeticInstantiation.run_exact
      q composition h1Z copyActive mu hq hc hh ha hm
  refine ⟨out, ?_, hcanon, ?_⟩
  · rw [AspisR1SelectedMaskProbe.terminal_parts_caller_to_arithmetic_tail
      compositionCaller public1 claims point zerocheck_point lambda chi theta mu
      composition h1Z copyActive c1 mask_only g hcaller]
    rw [heq]
    simp only [bind_tc_ok]
    change (do
      let out ← AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run
        q composition h1Z copyActive mu
      ok (core.result.Result.Ok (out, c1, mask_only, g))) =
        .ok (core.result.Result.Ok (out, c1, mask_only, g))
    simp [hrun]
  · simpa [AspisR1.TerminalV4CurrentArithmeticInstantiation.laws,
      AspisR1.TerminalV4Constants.one_decode] using hdecode

#print axioms terminal_parts_success_of_caller_and_exact_value

end AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridgeV6
