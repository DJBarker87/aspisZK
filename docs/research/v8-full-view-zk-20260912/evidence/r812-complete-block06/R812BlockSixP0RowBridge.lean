import AspisV8R19.R812BlockSixP0SourceRow
import AspisV8R19.R812BlockSixP0CertificateRow
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixP0RowBridge
open AspisV8R19.R812BlockSixP0SourceRow AspisV8R19.R812BlockSixP0CertificateRow
open AspisV8R19.R816BlockSixSourceView AspisV8R19.R807SourceBlock01Binding AspisV8R19.R803LiteralSupplementaryEntries
noncomputable section
theorem p0_source_row_eq_certificate :
 (fun j : Fin 39 => fixedSourceMatrix (pointPosition 0) (block06Columns j)) =
 (fun j : Fin 39 => R747JointBlock39Preflight.A (⟨38,by decide⟩ : Fin 39) j) := by
 rw [source_p0_values, certificate_p0_values]
 rfl
#print axioms p0_source_row_eq_certificate
end
end AspisV8R19.R812BlockSixP0RowBridge
