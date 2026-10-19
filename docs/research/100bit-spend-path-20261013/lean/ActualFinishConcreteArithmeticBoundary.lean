import ActualFinishTerminalComparison
import ExtractedMaskCallerModel
import RawSemanticFieldOwnerAdapter

/-!
Concrete the three arithmetic/mask boundaries of the extracted finish model.
The only still-abstract fields are the unrelated array/circle/claim plumbing
and the actual public terminal method.  In particular, successful finish no
longer permits arbitrary mask/add/mul implementations.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter

abbrev FinishBoundaries := FinishModel.Boundaries

/-- Rewrap a fixed-length public-owner array in the selected mask carrier. -/
def mainArrayToProbeN {n : Usize} (values : Array MainQM n) : Array ProbeQM n :=
  ⟨values.val.map mainToProbe, by simpa using values.property⟩

/-- The selected mask implementation, transported across the exact
coordinate rewrapping between the finish and current mask field owners. -/
def extractedMainMask (c1 : Array MainQM 16#usize)
    (maskOnly : Array MainQM 10#usize) (g : MainQM)
    (point : Array MainQM 10#usize) : Result MainQM :=
  probeResultToMain
    (state_only_hiding.state_only_selected_mask_value
      (mainArrayToProbeN c1) (mainArrayToProbeN maskOnly) (mainToProbe g)
      (mainArrayToProbeN point))

/-- Preserve the finish-model environment while fixing its selected mask and
field arithmetic to the current extracted operations. -/
def withConcreteArithmetic (B : FinishBoundaries) : FinishBoundaries :=
  { B with
    mask := extractedMainMask
    add := extractedMainAdd
    mul := extractedMainMul }

theorem finish_success_calls_concrete_arithmetic
    (R : RoundModel.Boundaries) (B : FinishBoundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish R (withConcreteArithmetic B) D pub pre before
      challenges obs = ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 mask
        etaTerminal masked extra28,
      RoundModel.rounds R D pre before = ok (.Ok (running, out.alpha, afterRounds)) ∧
      (withConcreteArithmetic B).terminal pub out.claims out.alpha challenges =
        ok (.Ok terminal) ∧
      (withConcreteArithmetic B).fromFn 16#usize (FinishModel.closureFn9 D)
        out.claims = ok mask16 ∧
      (withConcreteArithmetic B).fromFn 10#usize (FinishModel.closureFn5 D)
        out.claims = ok mask10 ∧
      Array.index_usize out.claims 0#usize = ok claim0 ∧
      Array.index_usize claim0 27#usize = ok claim27 ∧
      extractedMainMask mask16 mask10 claim27
        out.alpha = ok mask ∧
      extractedMainMul challenges.eta terminal = ok etaTerminal ∧
      extractedMainAdd mask etaTerminal = ok masked ∧
      Array.index_usize out.extra 28#usize = ok extra28 ∧
      extractedMainAdd masked extra28 = ok running := by
  obtain ⟨running, afterRounds, terminal, mask16, mask10, claim0, claim27,
      mask, etaTerminal, masked, extra28, hrounds, hterminal, hm16, hm10,
      hc0, hc27, hmask, heta, hadd, hextra, hfinal⟩ :=
    AspisR1PublicPreparation.ActualFinishTerminalComparison.terminal_comparison_of_finish_success
      R (withConcreteArithmetic B) D pub pre
      before challenges obs out hfinish
  refine ⟨running, afterRounds, terminal, mask16, mask10, claim0, claim27,
      mask, etaTerminal, masked, extra28, hrounds, hterminal, hm16, hm10,
      hc0, hc27, ?_, ?_, ?_, hextra, ?_⟩
  · simpa only [withConcreteArithmetic] using hmask
  · simpa only [withConcreteArithmetic] using heta
  · simpa only [withConcreteArithmetic] using hadd
  · simpa only [withConcreteArithmetic] using hfinal

#print axioms finish_success_calls_concrete_arithmetic
end AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
