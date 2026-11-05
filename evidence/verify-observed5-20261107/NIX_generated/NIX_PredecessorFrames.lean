import NIX_PrefixFrames
import NIX_RecordAtOrigin
import NIX_DecodeFinish
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIX_PredecessorFrames
open AspisR1PrefixAggregateParser

theorem record_at (bytes frame : Slice U8) (row : U8) (offset finish : Usize)
 (run : r1_wire.parse_record_at bytes row offset=ok (.Ok (frame,finish))) :
 frame.val.length=NGX_PrefixGeometry.width row.val := by
 obtain ⟨payload,parsed⟩:=NIX_RecordAtOrigin.result bytes frame row offset finish run
 obtain ⟨tag,size,shape,length⟩:=NIH_RecordFraming.accepted row frame payload parsed
 rw [NIX_DecodeFinish.shape_size row tag size shape] at length
 exact length

/-- Aggregate producer provenance for every SAME stored record, derived from
that parser's return. This is not a successful claims/finish premise. -/
theorem aggregate (bytes : Slice U8) (pre : r1_wire.Prefix)
 (parsed : r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∀ i : Fin 27,(FJb_TailCell.cell pre.records i).val.length=NGX_PrefixGeometry.width i.val := by
 apply NIX_PrefixFrames.result r1_wire.parse_record_at bytes pre
 · intro row offset frame finish run
   exact record_at bytes frame row offset finish run
 · rw [←NGX_PrefixSource.source]
   exact parsed

#print axioms record_at
#print axioms aggregate
end AspisR1.NIX_PredecessorFrames
