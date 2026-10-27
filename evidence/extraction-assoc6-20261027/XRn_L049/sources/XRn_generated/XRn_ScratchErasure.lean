import XRk_Funs
import XRn_ResultPair
open Aeneas Aeneas.Std Result
open XRk_Release XRn_Carriers XRn_ResultTransport XRn_ResultPair
set_option autoImplicit false
namespace XRn_ScratchErasure
/-- Scratch is an output-only buffer for the value projection, on ALL outcomes.
This is independent of a selected successful run and keeps fail/div. -/
theorem erased_independent {H : Type} (D : aspis_core.digest.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old other : Array C.E 29#usize) :
 mapR Prod.fst (verifier.Prepared.new D sem v hash old)=
 mapR Prod.fst (verifier.Prepared.new D sem v hash other) := by
 unfold verifier.Prepared.new
 simp only [mapR_bind,map_let_pair,map_pair,map_if,map_flow,map_ok]
#print axioms erased_independent
end XRn_ScratchErasure
