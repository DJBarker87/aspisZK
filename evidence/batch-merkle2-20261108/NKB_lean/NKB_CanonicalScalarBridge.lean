import NKB_CanonicalCuts
import MultiproofConeEndian
set_option autoImplicit false
namespace NKB_CanonicalScalarBridge
open Aeneas Aeneas.Std Result AspisR1

def good (b : Array U8 4#usize) : Bool := decide ((core.num.U32.from_le_bytes b).val<2147483647)
def scalar (b : Array U8 4#usize) : Option U32 :=
 if good b then some (core.num.U32.from_le_bytes b) else none

/-- All-input emitted scalar parser law, retaining rejection as well as the
payload. Native caller discards the payload, but its full Option is identified. -/
theorem source (b : Array U8 4#usize) :
 AspisR1M31Parser.field.M31.from_le_bytes b=ok (scalar b) := by
 unfold AspisR1M31Parser.field.M31.from_le_bytes AspisR1M31Parser.field.P
 simp only [lift,bind_tc_ok,UScalar.le_equiv,show (2147483647#u32).val=2147483647 from rfl]
 by_cases h:(core.num.U32.from_le_bytes b).val<2147483647 <;>
   simp [scalar,good,h,show (2147483647≤(core.num.U32.from_le_bytes b).val)↔¬(core.num.U32.from_le_bytes b).val<2147483647 by omega]

/-- The guard checked by the actual native scalar cut is exactly the
retained mathematical byte-codec guard, on the same four bytes. -/
theorem retained (b : Array U8 4#usize) :
 good b=decide ((RetainedFieldByteCodec.decodeWordLE (M31ParserArray.arrayBytes b)).val<2147483647) := by
 unfold good
 congr 1
 exact propext (MultiproofConeEndian.strict_word_iff b)

theorem native_result (b : Array U8 4#usize) (out : NKB_CanonicalRange.ScanResult)
 (cut : NKB_CanonicalCuts.ReadCut (good b) out) :
 out=NKB_CanonicalOpening.reply (decide ((RetainedFieldByteCodec.decodeWordLE
   (M31ParserArray.arrayBytes b)).val<2147483647)) := by
 rw [←retained]
 exact NKB_CanonicalCuts.read_result (good b) out cut

theorem scalar_tag (b : Array U8 4#usize) : (scalar b).isSome=good b := by
 unfold scalar
 cases h:good b <;> rfl

/-- Concrete scalar child substitution through the actual caller's ignored
payload and Parse conversion, with neither a success nor canonicality premise. -/
theorem caller_result (b : Array U8 4#usize) :
 (do let parsed←AspisR1M31Parser.field.M31.from_le_bytes b
     ok (if parsed.isSome then (.Ok () : NKB_CanonicalRange.ScanResult) else .Err .Parse))=
 ok (NKB_CanonicalOpening.reply (good b)) := by
 rw [source]
 change ok (if (scalar b).isSome then (.Ok () : NKB_CanonicalRange.ScanResult) else .Err .Parse)=_
 rw [scalar_tag]
 rfl

#print axioms scalar_tag
#print axioms caller_result

#print axioms source
#print axioms retained
#print axioms native_result
end NKB_CanonicalScalarBridge
