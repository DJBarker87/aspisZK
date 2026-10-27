import XRu_ParserShapes
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRz_RecordTransport
open XRu_ParserShapes
/-- Frame transport for rows before field validation, split at each scalar
read so no whole parser normalization is required. -/
theorem source (row : U8) (bytes : Slice U8) (fields : ∀ payload : Slice U8,
 mapR (inner id error) (r1_wire.validate_record_fields row payload)=
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload) :
 mapR (inner id error) (r1_wire.parse_record row bytes)=
 AspisR1PrefixAggregateParser.r1_wire.parse_record row bytes := by
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
   bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  change mapR (inner id error) ((5#usize+size : Result Usize) >>= _) =
    ((5#usize+size : Result Usize) >>= _)
  rw [mapR_bind]
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
      · simp only [mapR_bind]
        congr 1
        funext payload
        split
        · rw [←fields payload]
          simp only [bind_map,mapR_bind]
          congr 1
          funext status
          cases status <;> rfl
        · rfl
#print axioms source
end XRz_RecordTransport
