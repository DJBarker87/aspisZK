import TerminalV4CurrentArithmeticSourceBridgeV15
import TerminalV4PartsCallerInversionV5
import TerminalV4PublicTerminalQM31SuccessInversionV5
import TerminalV4PublicTerminalQM31ActualPartsChunk10V3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.TerminalV4PublicTerminalArithmeticSoundness
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisR1.TerminalV4QM31Exact.QM31Exact
abbrev decode := AspisR1.TerminalV4QM31Exact.decode

/-- Soundness of actual terminal wrapper success through the current composition
and terminal arithmetic cuts. Canonical input/output-cell obligations for the
Poseidon-derived operands remain explicit. -/
theorem terminal_success_has_canonical_arithmetic_parts
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (self : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array QM 29#usize) 3#usize)
    (alpha : Array QM 10#usize) (c : state_only_prefix.r0.Challenges)
    (outerOut : QM)
    (hsuccess : terminal_qm31_with_evaluators poseidonEval semanticEval self claims alpha c =
      .ok (core.result.Result.Ok outerOut))
    (hzero : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        (c.zc.val[i.val]'(by simpa [c.zc.property] using i.isLt)))
    (hpoint : ∀ i : Fin 10,
      AspisR1.TerminalV4EqualityValueResultRefinement.Canonical
        (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)))
    (hoperands : ∀ sem selected composition c1 mask g h1Z copyActive,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval sem selected alpha c.lambda c.chi c.theta =
        .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) →
      Canonical composition ∧ Canonical h1Z ∧ Canonical copyActive ∧ Canonical c.mu) :
    ∃ selected sem composition c1 mask g h1Z copyActive partOut,
      pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
        poseidonEval semanticEval sem selected alpha c.lambda c.chi c.theta =
        .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) ∧
      partOut = outerOut ∧ Canonical partOut ∧
      decode partOut =
        (AspisR1.TerminalV4EqualityValueResultRefinement.expectedEquality c.zc alpha *
          decode composition + decode c.mu * decode h1Z) +
        (decode c.mu * decode c.mu) * ((1 - decode copyActive) * decode h1Z) := by
  obtain ⟨selected, sem, tuple, hgather, hsemantic, hparts, hfirst⟩ :=
    AspisR1SelectedMaskProbe.terminal_success_reaches_parts
      poseidonEval semanticEval self claims alpha c outerOut hsuccess
  rcases tuple with ⟨partOut, c1Part, maskPart, gPart⟩
  obtain ⟨composition, c1, mask, g, h1Z, copyActive, hcomp⟩ :=
    AspisR1.TerminalV4PartsCallerInversion.composition_success_of_parts_success
      poseidonEval semanticEval sem selected alpha c.lambda c.chi c.theta c.zc c.mu
      partOut c1Part maskPart gPart hparts
  let caller : TerminalPartsCompositionCaller := fun public1 claims point lambda chi theta =>
    pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta
  have hcaller : caller sem selected alpha c.lambda c.chi c.theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive)) := hcomp
  have hparts' : pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
      caller sem selected alpha c.lambda c.chi c.theta c.zc c.mu =
      .ok (core.result.Result.Ok (partOut, c1Part, maskPart, gPart)) := by
    simpa only [terminal_parts_from_composition_callers] using hparts
  obtain ⟨out, hout, houtCan, houtValue⟩ :=
    AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticSourceBridgeV15.terminal_parts_success_of_caller_and_exact_value
      caller sem selected alpha c.zc c.lambda c.chi c.theta c.mu
      composition h1Z copyActive c1 mask g hcaller hzero hpoint
      (hoperands sem selected composition c1 mask g h1Z copyActive hcomp).1
      (hoperands sem selected composition c1 mask g h1Z copyActive hcomp).2.1
      (hoperands sem selected composition c1 mask g h1Z copyActive hcomp).2.2.1
      (hoperands sem selected composition c1 mask g h1Z copyActive hcomp).2.2.2
  have htuple : (out, c1, mask, g) = (partOut, c1Part, maskPart, gPart) :=
    Result.ok.inj (hout.symm.trans hparts')
  have houtEq : out = partOut := congrArg Prod.fst htuple
  have houtOuter : out = outerOut := houtEq.trans hfirst
  exact ⟨selected, sem, composition, c1, mask, g, h1Z, copyActive, out,
    hcomp, houtOuter, houtCan, houtValue⟩

#print axioms terminal_success_has_canonical_arithmetic_parts
end AspisR1.TerminalV4PublicTerminalArithmeticSoundness
