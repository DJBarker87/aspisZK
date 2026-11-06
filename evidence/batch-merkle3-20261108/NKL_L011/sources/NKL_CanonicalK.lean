import NKB_CanonicalKBridge
set_option autoImplicit false
noncomputable section
namespace NKL_CanonicalK
open Aeneas Aeneas.Std Result AspisR1 NKB_CanonicalRange
open OraclePortCkptAbi4Decode CheckpointBytes3KDecode CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

/-- The four little-endian words of the SAME16 bytes used by K025-K028. -/
def guard (b : Array U8 16#usize) : Bool :=
 decide ((word b.to_slice b.property 0).val<2147483647) &&
 decide ((word b.to_slice b.property 1).val<2147483647) &&
 decide ((word b.to_slice b.property 2).val<2147483647) &&
 decide ((word b.to_slice b.property 3).val<2147483647)

theorem good_eq_guard (b : Array U8 16#usize) : NKB_CanonicalKBridge.good b=guard b := by
 simp only [NKB_CanonicalKBridge.good,Canonical,kWords,guard,decide_and]
 simp only [Bool.and_assoc]

theorem word_value (b : Array U8 16#usize) (j : Fin 4) :
 (word b.to_slice b.property j).val=
 b.val[4*j.val]!.val + 256*b.val[4*j.val+1]!.val +
 65536*b.val[4*j.val+2]!.val + 16777216*b.val[4*j.val+3]!.val := by
 rw [word,CheckpointBytes3WordMath.pack_value]
 simp only [Array.to_slice,Slice.val,List.getElem!_eq_getElem,
  show 4*j.val<b.val.length by have:=b.property;omega,
  show 4*j.val+1<b.val.length by have:=b.property;omega,
  show 4*j.val+2<b.val.length by have:=b.property;omega,
  show 4*j.val+3<b.val.length by have:=b.property;omega]
 omega

/-- Concrete child substitution at a K call: exact rejection guard and Unit
conversion, with no canonical-input or successful-child hypothesis. -/
theorem source (b : Array U8 16#usize) :
 (do let parsed←OraclePortCkptAbi2Extracted.decode_k_spec b.to_slice
     ok (if parsed.isSome then (.Ok () : ScanResult) else .Err .Parse))=
 ok (NKB_CanonicalOpening.reply (guard b)) := by
 rw [NKB_CanonicalKBridge.source,good_eq_guard]

theorem native_result (b : Array U8 16#usize) (out : ScanResult)
 (cut : NKB_CanonicalCuts.ReadCut (guard b) out) :
 out=NKB_CanonicalOpening.reply (NKB_CanonicalKBridge.good b) := by
 rw [good_eq_guard]
 exact NKB_CanonicalCuts.read_result (guard b) out cut

set_option pp.proofs false
#print source
#print axioms good_eq_guard
#print axioms word_value
#print axioms source
#print axioms native_result
end NKL_CanonicalK
end
