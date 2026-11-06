import NJC_EReaderResults
set_option autoImplicit false
noncomputable section
namespace NKK_DecoderDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode

/-- Every successful E decoder reply belongs to the native E::new oracle's
canonical range. This domain is discharged from the actual decoder guard. -/
theorem e (b : Array U8 32#usize)
 (value : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
 (returned : NJC_EReaderResults.naturalE b=.Ok value) :
 CanonicalWide (CheckpointBytes3Namespaces.toE value) := by
 unfold NJC_EReaderResults.naturalE at returned
 dsimp only at returned
 split at returned
 · rename_i canonical
   cases returned
   simpa only [CheckpointBytes3Namespaces.toE,CheckpointBytes3Namespaces.fromE,
    CheckpointBytes3Namespaces.toK,CheckpointBytes3Namespaces.fromK] using canonical
 · cases returned

theorem k (b : Array U8 16#usize)
 (value : AspisR1Stage2.aspis_core.field.QM31)
 (returned : NJC_ReaderResults.naturalK b=.Ok value) :
 Canonical (CheckpointBytes3Namespaces.toK value) := by
 unfold NJC_ReaderResults.naturalK at returned
 dsimp only at returned
 split at returned
 · rename_i canonical
   cases returned
   simpa only [CheckpointBytes3Namespaces.toK,CheckpointBytes3Namespaces.fromK] using canonical
 · cases returned

#print axioms e
#print axioms k
end NKK_DecoderDomain
