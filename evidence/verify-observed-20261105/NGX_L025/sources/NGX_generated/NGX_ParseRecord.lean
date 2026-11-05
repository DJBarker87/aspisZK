import NGX_Payload
import NFU_RowDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NGX_ParseRecord
abbrev Error := AspisR1PrefixAggregateParser.r1_wire.Error
abbrev Validation := U8 → Slice U8 → Result (core.result.Result Unit Error)

def computation (validate : Validation) (row : U8) (record1 : Slice U8) :
 Result (core.result.Result (Slice U8) Error) := do
 let shape ← AspisR1PrefixAggregateParser.r1_wire.row_shape row
 match shape with
 | none => ok (.Err .InvalidRow)
 | some (tag,size) => do
  let length ← 5#usize+size
  if Slice.len record1 != length then ok (.Err (.Length row)) else do
   let first ← Slice.index_usize record1 0#usize
   if first != tag then ok (.Err (.Tag row)) else do
    let b1 ← Slice.index_usize record1 1#usize
    let b2 ← Slice.index_usize record1 2#usize
    let b3 ← Slice.index_usize record1 3#usize
    let b4 ← Slice.index_usize record1 4#usize
    let encoded := core.num.U32.from_le_bytes (Array.make 4#usize [b1,b2,b3,b4])
    if UScalar.cast .Usize encoded != size then ok (.Err (.Length row)) else do
     let payload ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) record1 {start:=5#usize}
     if row≥14#u8 then do
      let result ← validate row payload
      match result with
      | .Err error => ok (.Err error)
      | .Ok _ => ok (.Ok payload)
     else ok (.Ok payload)

theorem try_result {A : Type} (result : core.result.Result A Error) (payload : Slice U8) :
 (do
   let cf ← core.result.Result.Insts.CoreOpsTry.branch result
   match cf with
   | .Continue _ => ok (.Ok payload)
   | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (Slice U8) (core.convert.FromSame Error) residual) =
 (match result with | .Err error => ok (.Err error) | .Ok _ => ok (.Ok payload)) := by
 cases result <;> rfl


theorem source (row : U8) (record1 : Slice U8) :
 AspisR1PrefixAggregateParser.r1_wire.parse_record row record1 =
 computation AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row record1 := by
 unfold AspisR1PrefixAggregateParser.r1_wire.parse_record computation
 simp only [try_result]
 cases h : AspisR1PrefixAggregateParser.r1_wire.row_shape row <;>
   simp only [h,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i shape
 cases shape with
 | none => rfl
 | some pair => cases pair; rfl

/-- Domain of the CLOSED field validator is produced by the actual row-shape
helper and the SAME passed length gate; canonicality is not assumed. -/
theorem validator_domain (row tag : U8) (size : Usize) (framed payload : Slice U8)
 (shape : AspisR1PrefixAggregateParser.r1_wire.row_shape row=ok (some (tag,size)))
 (framed_length : framed.val.length=5+size.val)
 (same_bytes : payload.val=framed.val.drop 5) : payload.val.length≤3712 := by
 have h := (NFU_RowDomains.parser_shape row tag size shape).1
 rw [same_bytes,List.length_drop,framed_length]
 omega
#print axioms try_result
#print axioms source
#print axioms validator_domain
end AspisR1.NGX_ParseRecord
