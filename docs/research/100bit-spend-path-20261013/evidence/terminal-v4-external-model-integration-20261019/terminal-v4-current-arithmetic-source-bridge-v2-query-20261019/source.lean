import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4TerminalPartsArithmeticJoinChunk13V2
import TerminalV4CurrentArithmeticContractV2

open Aeneas Aeneas.Std Result
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridge
open AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract

abbrev QM := field.QM31

/-- The actual generated terminal-parts caller reduces to the proved suffix
once equality_value has returned its canonical field result. -/
theorem terminal_parts_success_of_caller_and_exact_value
    {K : Type} [Add K] [Sub K] [Mul K]
    (laws : Laws K)
    (compositionCaller : TerminalPartsCompositionCaller)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array field.QM31 84#usize)
    (point zerocheck_point : Array field.QM31 10#usize)
    (lambda chi theta mu composition h1Z copyActive : field.QM31)
    (c1 : Array field.QM31 16#usize)
    (mask_only : Array field.QM31 10#usize)
    (g q : field.QM31)
    (hcaller : compositionCaller public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask_only, g, h1Z, copyActive)))
    (heq : pool_v1.pair_forest_semantic_terminal.equality_value
      zerocheck_point point = .ok q)
    (hq : laws.canonical q) (hc : laws.canonical composition)
    (hh : laws.canonical h1Z) (ha : laws.canonical copyActive)
    (hm : laws.canonical mu) :
    ∃ out, pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      compositionCaller public1 claims point lambda chi theta zerocheck_point mu =
        .ok (core.result.Result.Ok (out, c1, mask_only, g)) ∧
      laws.canonical out ∧
      laws.decode out =
        (laws.decode q * laws.decode composition + laws.decode mu * laws.decode h1Z) +
        (laws.decode mu * laws.decode mu) *
          ((laws.one - laws.decode copyActive) * laws.decode h1Z) := by
  obtain ⟨out, hrun, houtCanonical, houtDecode⟩ :=
    AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run_exact
      laws q composition h1Z copyActive mu hq hc hh ha hm
  refine ⟨out, ?_, houtCanonical, houtDecode⟩
  rw [AspisR1SelectedMaskProbe.terminal_parts_caller_to_arithmetic_tail
    compositionCaller public1 claims point zerocheck_point lambda chi theta mu
    composition c1 mask_only g h1Z copyActive hcaller]
  simp [AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run,
    heq, hrun]

#print axioms terminal_parts_success_of_caller_and_exact_value
end AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridge
