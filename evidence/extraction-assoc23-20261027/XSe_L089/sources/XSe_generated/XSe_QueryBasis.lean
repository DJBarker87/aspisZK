import XSe_AccumulateBasis
import XSc_QueryCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_QueryBasis
/-- Every actual successful query establishes canonicality of its SAME basis
before the pending row loop. No per-row basis premise is supplied. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (run : verifier.candidate.query_values proof p a g obs geo pending=ok (.Ok (out,after))) :
 ∃ (basis : XSe_BasisUpdate.Basis) (rows : verifier.BatchedWeights),
 XSe_BasisUpdate.Canonical basis ∧
 verifier.accumulate_batched_with_node_loop1
  {start:=0#usize,«end»:=alloc.vec.Vec.len a.weights}
  a.weights a.power a.next pending (alloc.vec.Vec.len a.weights) basis=ok rows := by
 obtain ⟨q,node,value,_,hacc,_,_⟩ := XSc_QueryCuts.source proof p a out g obs geo pending after run
 exact XSe_AccumulateBasis.source p a out node value pending after hacc
#print axioms source
end XSe_QueryBasis
