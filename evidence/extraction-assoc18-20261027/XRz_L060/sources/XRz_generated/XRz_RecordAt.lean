import XRz_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRz_RecordAt
open XRu_ParserShapes
theorem source (row : U8) (bytes : Slice U8) (offset : Usize)
 (fields : ∀ payload : Slice U8,
 mapR (inner id error) (r1_wire.validate_record_fields row payload)=
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload) :
 mapR (inner id error) (r1_wire.parse_record_at bytes row offset)=
 AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes row offset := by
 unfold r1_wire.parse_record_at AspisR1PrefixAggregateParser.r1_wire.parse_record_at
 rw [XRu_ParserShapes.source row]
 simp only [mapR_bind]
 congr 1
 funext shape
 congr 1
 funext pair
 rcases pair with ⟨tag,size⟩
 dsimp! only
 simp only [mapR_bind]
 congr 1
 funext length
 congr 1
 funext stop
 congr 1
 funext selected
 cases selected with
 | none => rfl
 | some record =>
  simp only [core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [←XRz_RecordTransport.source row record fields]
  simp only [mapR_bind,bind_map]
  congr 1
  funext result
  cases result <;> rfl
#print axioms source
end XRz_RecordAt
