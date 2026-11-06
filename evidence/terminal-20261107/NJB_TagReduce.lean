import NJB_TagRaw
import ExtractedMaskReducer
set_option autoImplicit false
namespace AspisR1.NJB_TagReduce
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer (P)
theorem reduce (raw : U64) :
 ∃ out,FIq_Native.field.M31.reduce_u64 raw=ok out ∧ out.val=raw.val%P ∧ out.val<P := by
 rw [FIv_NativeArithmetic.m31_reduce]
 exact ExtractedMaskReducer.current_wrapper_mod raw
theorem add (x y : U32) (hx : x.val<P) (hy : y.val<P) :
 ∃ out,FIq_Native.field.M31.add x y=ok out ∧ out.val=(x.val+y.val)%P ∧ out.val<P := by
 rw [FIv_NativeArithmetic.m31_add]
 exact ExtractedMaskM31AddSub.current_add_mod x y hx hy
def reference (old : U32) (raw : U64) : Result U32 := do
 let residue ← FIq_Native.field.M31.reduce_u64 raw
 FIq_Native.field.M31.add old residue
theorem result (old : U32) (raw : U64) (canonical : old.val<P) :
 ∃ out,reference old raw=ok out ∧ out.val=(old.val+raw.val%P)%P ∧ out.val<P := by
 obtain ⟨r,cr,vr,hr⟩ := reduce raw
 obtain ⟨out,co,vo,ho⟩ := add old r canonical hr
 refine ⟨out,?_,?_,ho⟩
 · simp only [reference,cr,co,bind_tc_ok]
 · simpa only [vr] using vo
#print result
#print axioms reduce
#print axioms add
#print axioms result
end AspisR1.NJB_TagReduce
