import NGA_NativeOps
set_option autoImplicit false
noncomputable section
namespace NGH_QSquareRef
open Aeneas Aeneas.Std Result AspisR1.FIo_FieldBridge

def run (x : NQ) : Result NQ := do
 let a ← FIo_Native.aspis_core.field.CM31.square x.c0
 let b ← FIo_Native.aspis_core.field.CM31.square x.c1
 let r ← FIo_Native.aspis_core.field.mul_by_r b
 let lo ← FIo_Native.aspis_core.field.CM31.add a r
 let ab ← FIo_Native.aspis_core.field.CM31.mul x.c0 x.c1
 let hi ← FIo_Native.aspis_core.field.CM31.add ab ab
 ok ⟨lo,hi⟩

theorem model_eq (x : NQ) : run x=FIo_Native.aspis_core.field.QM31.square x := rfl

theorem cohort (x : NQ) (hx : NGA_NativeOps.Canon x) :
 ∃ out, run x=ok out ∧ NGA_NativeOps.Canon out ∧
 NGA_NativeOps.decode out=NGA_NativeOps.decode x*NGA_NativeOps.decode x := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_NativeOps.square x hx
 exact ⟨out,(model_eq x).trans ho,hc,hv⟩

#print axioms model_eq
#print axioms cohort
end NGH_QSquareRef
end
