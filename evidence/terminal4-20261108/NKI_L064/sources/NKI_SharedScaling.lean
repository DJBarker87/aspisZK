import NJL_SharedRoot
import NKI_WeightedDomains
import NKI_ArrayCanonicalEq
import RPv_FIy_Scaling
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_SharedScaling
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical decoded)
/-- The optimized shared-selector230/228 child agrees with the complete
old33cell scale+preweighted caller, including both boundary groups. -/
theorem source (packed : Array NQ 24#usize) (values : Array NQ 33#usize) (selector : NQ)
 (hp : canonical packed) (hv : canonical values) (hs : Canon selector) :
 (do let scaled←FIy_ScaleReadback.run values selector
     pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize scaled)=NJL_SharedRoot.reference packed values selector := by
 obtain ⟨weighted,after,calls,refcall,trace,oldcall,ha,va⟩ := NJL_SharedRoot.source packed values selector hp hv hs
 obtain ⟨scaled,scaleCall,hscaled,vscaled⟩ := FIy_Scaling.total values selector hv hs
 have w:=NKI_WeightedDomains.source values weighted selector hv hs calls
 have same : scaled=weighted := NKI_ArrayCanonicalEq.source scaled weighted hscaled w.1 (vscaled.trans w.2.symm)
 rw [scaleCall,bind_tc_ok,same,oldcall,refcall]
#print axioms source
end AspisR1.NKI_SharedScaling
end
