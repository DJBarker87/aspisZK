import R1Z.PV_RDCD5_V197Restored
set_option autoImplicit false
namespace R1Z.PV_RDCD5_V197ConsumerReplay
open Aeneas Aeneas.Std Result
theorem v197_corrected :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) = PV_RDCD4_BytesSource.qm [] :=
  PV_RDCD5_ParserErrors.carrier_agreement _
#print axioms v197_corrected
end R1Z.PV_RDCD5_V197ConsumerReplay
