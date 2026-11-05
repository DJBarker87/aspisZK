import NHM_SharedHigh
import NHM_DotResult
import NHI_TensorOuterStep
set_option autoImplicit false
namespace NHX_HighDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev W := FIo_Native.weights.Weights
abbrev Row := Array (Array NQ 4#usize) 5#usize
abbrev Factors := NHI_TensorOuterStep.Factors

/-- Reuse the tensor packet's canonical factor invariant; no different
canonical witness is selected for the scalar or high-dot children. -/
theorem row (w : W) (hf : Factors w) (k : Usize) (hk : k.val<5) :
 let r:=NHI_ScalarDomain.pick w.factors k.val hk
 Array.index_usize w.factors k=ok r ∧
 (∀ d (hd : d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick r d hd)) :=
 ⟨NHI_ScalarDomain.index w.factors k hk,hf k.val hk⟩

theorem scale (r : Row) (ap0 ap1 : Array NE 4#usize)
 (hr : ∀ d (hd : d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick r d hd))
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x) :
 ∃ q0 q1 a b out,
 Array.index_usize r 0#usize=ok q0 ∧ Array.index_usize r 1#usize=ok q1 ∧
 FIo_Native.weights.Weights.scalar_factor q0 ap0=ok a ∧ canonE a ∧
 FIo_Native.weights.Weights.scalar_factor q1 ap1=ok b ∧ canonE b ∧
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a b=ok out ∧ canonE out := by
 let q0:=NHI_ScalarDomain.pick r 0 (by decide)
 let q1:=NHI_ScalarDomain.pick r 1 (by decide)
 obtain ⟨s,a,hs,cs,hsa,ca,hv⟩:=NHI_Scalar.total q0 ap0 ha (hr 0 (by decide))
 obtain ⟨t,b,ht,ct,hsb,cb,hw⟩:=NHI_Scalar.total q1 ap1 hb (hr 1 (by decide))
 obtain ⟨out,ho,co,_⟩:=LPi_TowerValues.wide_mul a b ca cb
 exact ⟨q0,q1,a,b,out,NHI_ScalarDomain.index r 0#usize (by decide),
 NHI_ScalarDomain.index r 1#usize (by decide),hsa,ca,hsb,cb,ho,co⟩

/-- High-dot canonicality concerns the actual SAME successful child reply.
It is derived from the CLOSED child and never required as a success premise. -/
theorem high_reply (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize) (x : NE)
 (run : NHM_HighDot.reference partials coeffs=ok (.Ok x)) : canonE x :=
 NHM_DotResult.high partials coeffs x (by rwa [NHM_HighDot.cohort])

#print axioms row
#print axioms scale
#print axioms high_reply
end NHX_HighDomain
