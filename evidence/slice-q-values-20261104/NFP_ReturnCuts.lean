import NFP_SuffixCuts
import NFP_ObserverErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_ReturnCuts
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody

def finish (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : E) (pending : verifier.BatchedWeights) : Result Out := do
 let (after,b) ← verifier.accumulate_batched_with_node ops p a node value pending
 ops.op19 none (.Query a.next)
 ok (.Ok (after,b))

/-- The deployed phase no-op preserves the complete returned owned carrier.
Error and divergence in accumulation propagate before the phase position. -/
theorem erased (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : E) (pending : verifier.BatchedWeights) :
 finish (NFP_ObserverErasure.erase ops) p a node value pending =
 (do let result ← verifier.accumulate_batched_with_node (NFP_ObserverErasure.erase ops) p a node value pending
     ok (.Ok result)) := by
 unfold finish
 cases h : verifier.accumulate_batched_with_node (NFP_ObserverErasure.erase ops) p a node value pending <;> rfl

/-- Instantiating the native unconstrained child reply by its actual model
preserves the exact typed caller continuation. No whole-output hypothesis. -/
theorem continuation (ops : Ops) (a : verifier.Accumulator)
 (after : verifier.Accumulator × verifier.BatchedWeights) :
 (do (NFP_ObserverErasure.erase ops).op19 none (.Query a.next)
     ok (.Ok after) : Result Out) = ok (.Ok after) := rfl
#print axioms erased
#print axioms continuation
end AspisR1.NFP_ReturnCuts
end
