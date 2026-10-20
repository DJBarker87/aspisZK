import R1FinalSoundnessBin
import RawExtractorFixedProtocolEnvelope

/-! Fixed-coordinate instances of the final soundness cost consumer. The
coordinate premise is discharged; the implementation ledger is explicitly
retained. No assertion of a completed instrumented extractor is made here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessFixedProtocolBin
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorFixedProtocolPolynomial
open RawCutProverCompiler

theorem uniform_cost
    (implementation : Nat → RawExtractorCostComposedBin.CostedExtractor)
    (p : Parameters)
    (h_M10_ledger : ∀ Q, RawExtractorCostComposedBin.LedgerRefinement
      (implementation Q) (family p Q) Q)
    (Q : Nat) (run : RunView) (ha : run.2.2 = true)
    (hlog : run.1.length ≤ Q + 1161) :
    AspisV8R19.OracleResampling.mean (fun coins : Coins =>
      (((implementation Q).eval run coins).2.total : ℚ)) ≤
      (Nat.cast ((RawExtractorCostComposedBin.queryPolynomial
        p.overheadConstant 1 (slack p)).eval Q) : ℚ) :=
  R1FinalSoundnessBin.uniform_cost implementation (family p)
    p.overheadConstant 1 (slack p) h_M10_ledger (coordinates p) Q run ha hlog

/-- A sharper degree-one envelope, using fixed protocol coordinates directly
rather than the higher-degree all-coordinates-varying diagonal. -/
theorem uniform_linear_cost
    (implementation : Nat → RawExtractorCostComposedBin.CostedExtractor)
    (p : Parameters)
    (h_M10_ledger : ∀ Q, RawExtractorCostComposedBin.LedgerRefinement
      (implementation Q) (family p Q) Q)
    (Q : Nat) (run : RunView) (ha : run.2.2 = true)
    (hlog : run.1.length ≤ Q + 1161) :
    AspisV8R19.OracleResampling.mean (fun coins : Coins =>
      (((implementation Q).eval run coins).2.total : ℚ)) ≤
      (Nat.cast (RawExtractorFixedProtocolEnvelope.constant p * (Q + 1161)) : ℚ) :=
  RawExtractorFixedProtocolEnvelope.accepted_linear_cost implementation p
    h_M10_ledger Q run ha hlog

#print axioms uniform_cost
#print axioms uniform_linear_cost
end AspisR1.R1FinalSoundnessFixedProtocolBin
end
