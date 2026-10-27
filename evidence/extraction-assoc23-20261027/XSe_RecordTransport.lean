import XSe_PayloadDomain
import XRz_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSe_RecordTransport
open XRu_ParserShapes
/-- Complete record parser equation with the validator's domain DERIVED from
the same actual header and selected payload. No universal callback premise. -/
theorem source (row : U8) (bytes : Slice U8) :
 mapR (inner id error) (r1_wire.parse_record row bytes)=
 AspisR1PrefixAggregateParser.r1_wire.parse_record row bytes := by
 unfold r1_wire.parse_record AspisR1PrefixAggregateParser.r1_wire.parse_record
 rw [XRu_ParserShapes.source row]
 cases shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row with
 | fail e => rfl
 | div => rfl
 | ok optional =>
  cases optional with
  | none => rfl
  | some pair =>
   rcases pair with ⟨tag,size⟩
   have hshape : r1_wire.row_shape row=ok (some (tag,size)) := (XRu_ParserShapes.source row).trans shape
   simp only [core.option.Option.ok_or,AspisR1PrefixAggregateParser.core.option.Option.ok_or,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
   change mapR (inner id error) ((5#usize+size : Result Usize) >>= _) =
     ((5#usize+size : Result Usize) >>= _)
   rw [mapR_bind]
   apply (bind_eq_iff _ _ _).mpr
   intro full hfull
   split
   · rfl
   · rename_i sameLength
     have len : Slice.len bytes=full := by simpa only [bne_iff_ne,not_not] using sameLength
     simp only [mapR_bind]
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
         apply (bind_eq_iff _ _ _).mpr
         intro payload selected
         split
         · have domain := XSe_PayloadDomain.source row tag size full bytes payload hshape hfull len selected
           rw [←XSe_ValidatorTransport.source row payload domain]
           simp only [bind_map,mapR_bind]
           congr 1
           funext status
           cases status <;> rfl
         · rfl
#print axioms source
end XSe_RecordTransport
