import NJB_PackLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PackLinearity
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
def pack (v : Fin 4 → K) : K := v 0+iBasis*v 1+uBasis*v 2+(iBasis*uBasis)*v 3
theorem model (v : Fin 4 → NQ) : NJB_PackLaw.model v=pack (fun i=>decode (v i)) := rfl
/-- Optimized shared-selector packing may move the SAME selector outside a
four-lane pack, including either zero-padded boundary group. -/
theorem scale (selector : K) (v : Fin 4 → K) :
 pack (fun i=>selector*v i)=selector*pack v := by unfold pack;ring
theorem add (v w : Fin 4 → K) : pack (fun i=>v i+w i)=pack v+pack w := by unfold pack;ring
theorem zero : pack (fun _=>0)=0 := by simp [pack]
#print scale
#print axioms model
#print axioms scale
#print axioms add
#print axioms zero
end AspisR1.NJB_PackLinearity
end
