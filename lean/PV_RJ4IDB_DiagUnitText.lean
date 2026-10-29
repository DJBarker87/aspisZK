import PV_RJ4IDB_Diag2Adapter
import PV_DIAG2_ErrorText
import PV_DIAG2_Exhaustion
import PV_DIAG2_MaskMapper
import PV_DIAG2_Rejection
set_option autoImplicit false
namespace PV_RJ4IDB
open Aeneas Aeneas.Std
/-- The native unit-variant spelling is a proved available component. Actual
variant occurrence, PCs, formatting, delivery and earlier prefixes remain. -/
theorem unit_variant_content (e : R1Z.ProverRwFull.verifier.Error) (pcs : List Nat) :
 PV_DIAG2.reportError (PV_DIAG2.exportError (R1Z.ProverRwRetryModel.error e)) pcs "" false =
 ⟨[.returned (PV_DIAG2.exportError (R1Z.ProverRwRetryModel.error e)),
 .stderr ("Error: " ++ PV_DIAG2.nativeUnitDebug e ++ "\n")],.value 1⟩ :=
 PV_DIAG2.native_report_disabled e pcs

theorem unit_content_retained (e : R1Z.ProverRwFull.verifier.Error) (pcs : List Nat)
 (before : List PV_DIAG2.Effect) :
 diagnostics2 (diag2Events (before ++
 (PV_DIAG2.reportError (PV_DIAG2.exportError (R1Z.ProverRwRetryModel.error e)) pcs "" false).effects)) =
 before ++ [.returned (PV_DIAG2.exportError (R1Z.ProverRwRetryModel.error e)),
 .stderr ("Error: " ++ PV_DIAG2.nativeUnitDebug e ++ "\n")] := by
 rw [diag2_recover,unit_variant_content]
 rfl
#print axioms unit_variant_content
#print axioms unit_content_retained
end PV_RJ4IDB
