import R1Z.PV_RDCD5_ParserErrors
import R1Z.PV_RDCD4_V197
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_V197Restored
open Aeneas Aeneas.Std Result
/-- Original op71 parser-source boundary, every Slice, complete Result. The
existing dictionary's op71_source law consumes precisely this source function. -/
theorem parser_instance (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes =
      PV_RDCD5_V197.reference bytes.val := by
  rw [PV_RDCD5_ParserTransport.quartic,PV_RDCD5_V197.source_reference]

/-- Full typed component-window transport on the original bounded borrowed
window. The bound describes the window operation, not the parser input domain. -/
theorem window_instance (bytes : List U8) (base : Nat) (h : base+8 ≤ bytes.length) :
    PV_RDCD4_BytesSource.cm (PV_RDCD4_SliceRange194.window bytes base (base+8)) =
      PV_RDCD5_ParserFlat.cmAt bytes base := PV_RDCD5_ParserFlat.cm_window bytes base h

/-- No returned borrow and no input mutation; failure remains in Result. -/
theorem input_frame (bytes : Slice U8) :
    (do let out ← ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes
        ok (out,bytes)) =
    (do let out ← PV_RDCD5_V197.reference bytes.val
        ok (out,bytes)) := by rw [parser_instance]

/-- The old rdcd4 draft is checked against the same corrected model. -/
theorem rdcd4_instance (bytes : Slice U8) :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes bytes =
      PV_RDCD4_V197.reference bytes.val := by
  rw [PV_RDCD5_ParserTransport.quartic,PV_RDCD4_V197.source_reference]

#print axioms parser_instance
#print axioms window_instance
#print axioms input_frame
#print axioms rdcd4_instance
end R1Z.PV_RDCD5_V197Restored
