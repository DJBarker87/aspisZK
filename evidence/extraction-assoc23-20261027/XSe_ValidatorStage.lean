import XSe_ByteDecoder
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ValidatorStage
abbrev OldWide := XSc_RecordFieldTypes.OW
abbrev OldError := AspisR1PrefixAggregateParser.r1_wire.Error
/-- One complete decoder/high-half validator stage, before enumeration. -/
def old (row : U8) (i : Usize) (s : Slice U8) :
 Result (core.result.Result Unit OldError) := do
 let value ← AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes s
 match value with
 | none => ok (.Err (.NonCanonical row i))
 | some w =>
   if w.c1.c0.a==0#u32 && w.c1.c0.b==0#u32 && w.c1.c1.a==0#u32 && w.c1.c1.b==0#u32
   then ok (.Ok ()) else ok (.Err (.NonCanonical row i))

def kit (row : U8) (i : Usize) (s : Slice U8) :
 Result (core.result.Result Unit OldError) := do
 let value ← _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s
 match value with
 | none => ok (.Err (.NonCanonical row i))
 | some w =>
   if w.c1.c0.a==0#u32 && w.c1.c0.b==0#u32 && w.c1.c1.a==0#u32 && w.c1.c1.b==0#u32
   then ok (.Ok ()) else ok (.Err (.NonCanonical row i))

theorem source (row : U8) (i : Usize) (s : Slice U8) : old row i s=kit row i s := by
 unfold kit
 rw [←XSe_ByteDecoder.source s]
 unfold XSc_RecordByteLength.mapped
 simp only [XRo_Join_ResultTransport.bind_map]
 unfold old
 congr 1
 funext value
 cases value <;> rfl
#print axioms source
end XSe_ValidatorStage
