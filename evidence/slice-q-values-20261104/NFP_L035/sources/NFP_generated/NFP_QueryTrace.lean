import NFP_TraceHead
import NFP_TraceFront
import NFP_TraceBack
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_QueryTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) : M Out := do
 let (u,q,dots) ← NFP_TraceHead.run base proof p a g
 let (inverse,_,values,bad) ← NFP_TraceFront.run base p a geometry u q dots
 if bad then pure (.Err verifier.Error.Query)
 else NFP_TraceBack.run base p a geometry pending inverse values

theorem erased (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
 (run ops proof p a g geometry pending).result =
 verifier.candidate.query_values (NFP_ObserverErasure.erase ops) proof p a g none geometry pending := by
 rw [NFP_QueryCuts.source]
 simp only [run,NFI_TraceResult.erase_bind,NFP_TraceHead.erased,NFP_TraceFront.erased,
  apply_ite,NFP_TraceBack.erased,pure_result,NFP_SuffixCuts.source] <;> rfl
#print axioms erased
end AspisR1.NFP_QueryTrace
end
