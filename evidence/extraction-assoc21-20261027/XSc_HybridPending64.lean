import XSc_QueryPendingReach
import XSc_QueryTermReach
import XRz_HybridCuts
import XRu_NewLength
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_HybridPending64
/-- Pending length64 is derived at EVERY successful reached prefix of the SAME
LPk-backed hybrid query execution, not postulated as a reserve/caller law. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : XRz_HybridTx1.tx1 XRz_HybridSampler.adopted D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (initial a : verifier.Accumulator) (geo : verifier.QueryGeometry) (pending0 pending : verifier.BatchedWeights),
 verifier.Accumulator.new .S2=ok (.Ok initial) ∧
 verifier.BatchedWeights.new initial.weights.deref=ok (.Ok pending0) ∧
 verifier.candidate.query_loop proof p initial g obs geo pending0 split=ok (.Ok (a,pending)) ∧
 pending0.raw.val.length=64 ∧ pending0.terms=0#usize ∧
 ∀ (a : verifier.Accumulator) (pending : verifier.BatchedWeights),
  XSc_QueryPath.Reached proof p g obs geo split (.Ok (initial,pending0)) (.Ok (a,pending)) →
  pending.raw.val.length=64 ∧ pending.terms=a.next := by
 obtain ⟨_,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
  _,_,_,_,hinit,_,_,hpending,hquery,_,_,_⟩ :=
  XRz_HybridCuts.source XRz_HybridSampler.adopted D pub physical proof split hash obs saved run
 have init := XRr_Initial64.init initial hinit
 have fresh := XRu_NewLength.source initial.weights.deref pending0 hpending
 have len : pending0.raw.val.length=64 := fresh.1.trans init.1
 refine ⟨p,g,initial,a,geo,pending0,pending,hinit,hpending,hquery,len,fresh.2,?_⟩
 intro a pending path
 refine ⟨(XSc_QueryPendingReach.reached proof p g obs geo split initial pending0 (.Ok (a,pending)) path).trans len,?_⟩
 have counter : pending0.terms=initial.next := fresh.2.trans init.2.symm
 exact XSc_QueryTermReach.reached proof p g obs geo split initial pending0 counter (.Ok (a,pending)) path
#print axioms source
end XSc_HybridPending64
