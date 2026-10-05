import AspisV8R19.R812BlockSixP2SourceRow
import AspisV8R19.R812BlockSixP2CertificateRow
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixP2RowBridge
open AspisV8R19.R812BlockSixP2SourceRow AspisV8R19.R812BlockSixP2CertificateRow
open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding AspisV8R19.R803LiteralSupplementaryEntries
noncomputable section
theorem p2_source_row_eq_certificate :
 (fun j : Fin 39 => fixedSourceMatrix (pointPosition 2) (block06Columns j)) =
 (fun j : Fin 39 => R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) j) := by
 rw [source_p2_values, certificate_p2_values]
 rfl
#print axioms p2_source_row_eq_certificate
end
end AspisV8R19.R812BlockSixP2RowBridge
