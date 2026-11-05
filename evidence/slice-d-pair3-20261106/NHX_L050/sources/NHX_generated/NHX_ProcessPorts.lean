import NHX_VecPort
import NHX_HighDomain
set_option autoImplicit false
namespace NHX_ProcessPorts
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev W := FIo_Native.weights.Weights

theorem tensor_domain (w : W) (k : Usize) (hk : k.val<5)
 (hf : NHI_TensorOuterStep.Factors w) : NHI_Tensor.Domain w k hk := by
 intro d hd first
 exact hf k.val hk d.val hd

/-- The SAME slice returned by tensor rebuilds the SAME scratch Vec. No new
allocation, independent scratch witness or successful-child premise. -/
theorem tensor (w : W) (k : Usize) (hk : k.val<5) (hf : NHI_TensorOuterStep.Factors w)
 (v : NHX_VecPort.Vec) (len : (alloc.vec.Vec.deref v).val.length=64)
 (ca : NHI_CellCanon.slice (alloc.vec.Vec.deref v)) :
 ∃ out,FIo_Native.weights.Weights.tensor w k 2#usize (alloc.vec.Vec.deref_mut v).1=ok out ∧
 NHI_CellCanon.slice (alloc.vec.Vec.deref ((alloc.vec.Vec.deref_mut v).2 out)) ∧
 (alloc.vec.Vec.deref ((alloc.vec.Vec.deref_mut v).2 out)).val.length=64 := by
 have len1:(alloc.vec.Vec.deref_mut v).1.val.length=64:=by rw [NHX_VecPort.borrow_value];exact len
 have ca1:NHI_CellCanon.slice (alloc.vec.Vec.deref_mut v).1:=by
  simpa only [NHI_CellCanon.slice,NHX_VecPort.borrow_value] using ca
 obtain ⟨run,canonical,size⟩:=NHI_Tensor.cohort w k hk (tensor_domain w k hk hf)
  (alloc.vec.Vec.deref_mut v).1 len1 ca1
 exact ⟨_,run,NHX_VecPort.back_canonical v _ canonical,NHX_VecPort.back_length v _ size⟩

/-- Actual selected-row scale packet for the two-fold ordinary branch. -/
theorem scale (w : W) (k : Usize) (hk : k.val<5) (hf : NHI_TensorOuterStep.Factors w)
 (ap0 ap1 : Array NE 4#usize) (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x) :
 ∃ row q0 q1 a b out,Array.index_usize w.factors k=ok row ∧
 Array.index_usize row 0#usize=ok q0 ∧ Array.index_usize row 1#usize=ok q1 ∧
 FIo_Native.weights.Weights.scalar_factor q0 ap0=ok a ∧ canonE a ∧
 FIo_Native.weights.Weights.scalar_factor q1 ap1=ok b ∧ canonE b ∧
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a b=ok out ∧ canonE out := by
 obtain ⟨ir,cr⟩:=NHX_HighDomain.row w hf k hk
 obtain ⟨q0,q1,a,b,out,i0,i1,sa,ca,sb,cb,ho,co⟩:=NHX_HighDomain.scale _ ap0 ap1 cr ha hb
 exact ⟨_,q0,q1,a,b,out,ir,i0,i1,sa,ca,sb,cb,ho,co⟩

#print axioms tensor_domain
#print axioms tensor
#print axioms scale
end NHX_ProcessPorts
