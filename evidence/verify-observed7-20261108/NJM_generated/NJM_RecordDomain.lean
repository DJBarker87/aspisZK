import NJM_SemanticDomain
set_option autoImplicit false
namespace AspisR1.NJM_RecordDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- SAME deterministic getter identifies the full record, not merely its row
or address. Its byte bound is derived from the accepted prefix. -/
theorem round {H : Type} (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (bound : r.val<10) (record : r1_wire.ValidatedRecord)
 (getter : r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record)) :
 record.row=NJG_RoundProducer.row r bound ∧ record.row.val≤24 ∧ record.framed.val.length=901 := by
 obtain ⟨same,call,row,framed⟩:=NJG_RoundProducer.framed bytes pre parsed r bound
 have equal : record=same := core.result.Result.Ok.inj (Result.ok.inj (getter.symm.trans call))
 subst same
 refine ⟨row,?_,framed⟩
 rw [row,NJG_RoundProducer.row_value]
 omega

/-- Returning semantic source reply lies in the native K073–076 domain. -/
theorem semantic {H : Type} (D : aspis_core.Digest32 H)
 (before after : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
 (bound : record.row.val≤24) (reply : core.result.Result aspis_core.field.QM31 r1_wire.Error)
 (call : (PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (reply,after)) :
 match reply with | .Ok _=>True | .Err (.RowOrder _ _)=>True | _=>False := by
 have good:=NJM_SemanticDomain.code D before record bound
 rw [call] at good
 cases reply with
 | Ok q => trivial
 | Err error => cases error <;> exact good

#print axioms round
#print axioms semantic
end AspisR1.NJM_RecordDomain
