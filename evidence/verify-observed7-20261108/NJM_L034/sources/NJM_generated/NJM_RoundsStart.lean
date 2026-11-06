import NJM_RoundsJoin
set_option autoImplicit false
namespace AspisR1.NJM_RoundsStart
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (Code run)

/-- Actual initial row14 getter/decoder/indexing. The ZERO alpha array is
created before the first step, exactly as the emitted body does. -/
def source {H : Type} (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 Result (core.result.Result (Carry H) r1_wire.Error) := do
 let reply ← r1_wire.Prefix.validated_record pre 14#u8
 match reply with
 | .Err error => ok (.Err error)
 | .Ok record =>
   let decoded ← AspisS1ExtractedRoundChildren.decodeMain 1#usize record 0#usize
   match decoded with
   | .Err error => ok (.Err error)
   | .Ok values =>
     let running ← Array.index_usize values 0#usize
     ok (.Ok (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t))

/-- The initial driver's canonical-alpha invariant is vacuous at index0,
independent of the decoded running value and every other field. -/
theorem initial {H : Type} (running : aspis_core.field.QM31) (t : r1_wire.SemanticTranscript H) :
 NJM_RoundsInvariant.Inv 0 (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t) :=
 NJG_CanonicalPrefix.initial _

/-- Initial source state is obtained from the CLOSED decoder at the SAME
accepted prefix. No successful child equation is supplied by the caller. -/
theorem packet {H : Type} (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) :
 ∃ running,source (PrefixAdapter.fromOld pre) t=
 ok (.Ok (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t)) := by
 have parse : PrefixAdapter.parseAccepted bytes=ok (.Ok (PrefixAdapter.fromOld pre)) := by
  simp only [PrefixAdapter.parseAccepted,parsed,bind_tc_ok]
 obtain ⟨record,values,getter,decode⟩:=JFv_SemanticDecode.initial bytes (PrefixAdapter.fromOld pre) parse
 simp only [source,getter,bind_tc_ok,decode]
 obtain ⟨running,index,_⟩:=WP.spec_imp_exists (Array.index_usize_spec values 0#usize (by simp))
 rw [index,bind_tc_ok]
 exact ⟨running,rfl⟩

#print axioms initial
#print axioms packet
end AspisR1.NJM_RoundsStart
