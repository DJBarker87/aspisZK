import AspisFormal.K1.V7Tag73ExactCleanK13MeasuredComposition
import AspisFormal.K1.V7Tag73Q16CountCertificateBridge

/-!
# Release count bridge for the clean measured K1.6 assembly

The semantic K1.3/K1.6 composition deliberately does not import the thousands
of generated compact-frontier count certificates.  This release-only leaf
connects that small semantic theorem graph to the frozen decimal error ledger.
It is checked when producing the release certificate, not on every source or
semantic edit.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactMeasuredCleanK16Assembly

open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73Q16CountCertificateBridge

noncomputable section

/-- The semantic K1.3 error expression is exactly the frozen release-ledger
expression once the generated cap-203 count certificate is installed. -/
theorem exactK13SemanticRawError_eq_exactK13IdealRawError :
    exactK13SemanticRawError = exactK13IdealRawError := by
  unfold exactK13SemanticRawError exactK13IdealRawError
    q16SemanticOneForestRawError exactQ16IdealRawError
  rw [semanticCompactFavourable_eq_exactK13CompactFavourable]

end

#print axioms exactK13SemanticRawError_eq_exactK13IdealRawError

end AspisK1.V7Tag73ExactMeasuredCleanK16Assembly
