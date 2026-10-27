import R1Z.PV_CB_CandidateCore
import R1Z.PV_CB_CandidateCodecs
import R1Z.PV_CB_CandidateField
import R1Z.PV_CB_CandidateZeroizing
import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op118 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : Array aspis_core.field.QM31 10#usize) :
    (selected base ops).op118 x = (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points (PV_CB_Op118Transport.encodeArray x)
      ok (PV_CB_Op118Transport.decodePoints value)) := by
  letI : ExternalTypes := native base
  change (PV_CB_Op118Exact.selected ops).op118 x = _
  exact R1Z.PV_CB_Op118Exact.op118_source ops x
#print axioms op118
theorem op229 (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    (selected base ops).op229 a b = PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a) (PV_CB_Op229Transport.encode base b) := by
  letI : ExternalTypes := native base
  change (PV_CB_Op229Source.selected base ops).op229 a b = _
  exact R1Z.PV_CB_Op229Source.op229_source base ops a b
#print axioms op229
end R1Z.PV_CB_CandidateDictionary

-- Audit both the published row laws and their joint projections.
#print axioms R1Z.PV_CB_TakeSource.op3_source
#print axioms R1Z.PV_CB_Op71Exact.op71_source
#print axioms R1Z.PV_CB_Op72Exact.op72_source
#print axioms R1Z.PV_CB_Op77Source.op77_source
#print axioms R1Z.PV_CB_Op80Exact.op80_source
#print axioms R1Z.PV_CB_Op82Source.op82_source
#print axioms R1Z.PV_CB_Op83Source.op83_source
#print axioms R1Z.PV_CB_Op84Exact.op84_source
#print axioms R1Z.PV_CB_Op86Source.op86_source
#print axioms R1Z.PV_CB_Op100Exact.op100_source
#print axioms R1Z.PV_CB_Op101Exact.op101_source
#print axioms R1Z.PV_CB_Op105Exact.op105_source
#print axioms R1Z.PV_CB_Op107Exact.op107_source
#print axioms R1Z.PV_CB_Op109Exact.op109_source
#print axioms R1Z.PV_CB_Op110Source.op110_source
#print axioms R1Z.PV_CB_Op111Source.op111_source
#print axioms R1Z.PV_CB_Op114Source.op114_source
#print axioms R1Z.PV_CB_Op118Exact.op118_source
#print axioms R1Z.PV_CB_Op127Source.op127_source
#print axioms R1Z.PV_CB_Op128Source.op128_source
#print axioms R1Z.PV_CB_Op130Source.op130_source
#print axioms R1Z.PV_CB_Op131Source.op131_source
#print axioms R1Z.PV_CB_Op229Source.op229_source
#print axioms R1Z.PV_CB_CandidateDictionary.op3
#print axioms R1Z.PV_CB_CandidateDictionary.op71
#print axioms R1Z.PV_CB_CandidateDictionary.op72
#print axioms R1Z.PV_CB_CandidateDictionary.op77
#print axioms R1Z.PV_CB_CandidateDictionary.op80
#print axioms R1Z.PV_CB_CandidateDictionary.op82
#print axioms R1Z.PV_CB_CandidateDictionary.op83
#print axioms R1Z.PV_CB_CandidateDictionary.op84
#print axioms R1Z.PV_CB_CandidateDictionary.op86
#print axioms R1Z.PV_CB_CandidateDictionary.op100
#print axioms R1Z.PV_CB_CandidateDictionary.op101
#print axioms R1Z.PV_CB_CandidateDictionary.op105
#print axioms R1Z.PV_CB_CandidateDictionary.op107
#print axioms R1Z.PV_CB_CandidateDictionary.op109
#print axioms R1Z.PV_CB_CandidateDictionary.op110
#print axioms R1Z.PV_CB_CandidateDictionary.op111
#print axioms R1Z.PV_CB_CandidateDictionary.op114
#print axioms R1Z.PV_CB_CandidateDictionary.op118
#print axioms R1Z.PV_CB_CandidateDictionary.op127
#print axioms R1Z.PV_CB_CandidateDictionary.op128
#print axioms R1Z.PV_CB_CandidateDictionary.op130
#print axioms R1Z.PV_CB_CandidateDictionary.op131
#print axioms R1Z.PV_CB_CandidateDictionary.op229

-- Generic/carrier/P6 helper audit for the newly discharged rows.
#print axioms R1Z.PV_CB_Op107Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op107Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_OptionDiscriminant.none_tag
#print axioms R1Z.PV_CB_OptionDiscriminant.some_tag
#print axioms R1Z.PV_CB_ArrayTransport.roundtrip
#print axioms R1Z.PV_CB_Op109RefTransport.native_roundtrip
#print axioms R1Z.PV_CB_Op109RefTransport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_wide_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_wide_roundtrip
#print axioms R1Z.PV_CB_Op109CanonicalBinding.reference_equation
#print axioms R1Z.PV_CB_Op118Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_points_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_points_roundtrip
