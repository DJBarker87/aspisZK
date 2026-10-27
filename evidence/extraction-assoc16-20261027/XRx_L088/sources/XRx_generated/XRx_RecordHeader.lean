import XRu_ParserShapes
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRx_RecordHeader
open XRu_ParserShapes
/-- Frame transport for rows before field validation, split at each scalar
read so no whole parser normalization is required. -/
theorem source (row : U8) (bytes : Slice U8) (early : row.val<14) :
 mapR (inner id error) (r1_wire.parse_record row bytes)=
 AspisR1PrefixAggregateParser.r1_wire.parse_record row bytes := by
 have early' : ¬row≥14#u8 := by scalar_tac
 unfold r1_wire.parse_record AspisR1PrefixAggregateParser.r1_wire.parse_record
 rw [XRu_ParserShapes.source row]
 simp only [mapR_bind]
 congr 1
 funext o
 cases o with
 | none => rfl
 | some pair =>
  rcases pair with ⟨tag,size⟩
  simp only [core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
   bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mapR_bind]
  congr 1
  funext full
  split
  · rfl
  · simp only [mapR_bind]
    congr 1
    funext actual
    split
    · rfl
    · simp only [mapR_bind]
      congr 1
      funext b1
      congr 1
      funext b2
      congr 1
      funext b3
      congr 1
      funext b4
      simp only [lift,bind_tc_ok,mapR_bind]
      split
      · rfl
      · simp only [mapR_bind,if_neg early']
        rfl
#print axioms source
end XRx_RecordHeader
