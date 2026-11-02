import NEI_ReduceRefRaw.Funs
import NEI_DotReduction
set_option autoImplicit false
noncomputable section
namespace NEI_ReduceRefLaw
open Aeneas Aeneas.Std Result AspisR1
theorem same (x : U64) : NEI_ReduceRefRaw.NEI_reduce_ref x =
 FIo_Native.fast_pairing.canonical.reduce x := by
 unfold NEI_ReduceRefRaw.NEI_reduce_ref FIo_Native.fast_pairing.canonical.reduce
 simp only [NEI_ReduceRefRaw.P,FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok,FIo_ReduceFacts.shr31]
 rfl
theorem actual_reference (x : U64) :
 NEI_DotFinishRaw.fast_pairing.canonical.reduce x = NEI_ReduceRefRaw.NEI_reduce_ref x := by
 rw [same,NEI_DotReduction.same]
theorem frame {S : Type} (x : U64) (state : S) :
 (do let z ← NEI_DotFinishRaw.fast_pairing.canonical.reduce x;ok (z,state)) =
 (do let z ← FIo_Native.fast_pairing.canonical.reduce x;ok (z,state)) := by
 rw [NEI_DotReduction.same]
#print axioms same
#print axioms actual_reference
#print axioms frame
end NEI_ReduceRefLaw
end
