import XRu_NewLength
import XRr_CandidateCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_CandidatePending64
/-- The pending64 initialization and query are cuts of THIS pinned kit run.
The excluded sampler prevents promotion to the LPk-backed hybrid by name. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (initial : verifier.Accumulator) (geo : verifier.QueryGeometry)
  (pending0 : verifier.BatchedWeights) (a : verifier.Accumulator) (pending : verifier.BatchedWeights),
 verifier.Accumulator.new .S2=ok (.Ok initial) ∧
 verifier.BatchedWeights.new initial.weights.deref=ok (.Ok pending0) ∧
 pending0.raw.val.length=64 ∧ pending0.terms=0#usize ∧
 verifier.candidate.query_loop proof p initial g obs geo pending0 split=ok (.Ok (a,pending)) := by
 obtain ⟨splitEq,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
  hshape,hscan,hzero,hprepare,hinit,hbatch,hgeo,hpending,hquery,hrestore,hfinish,hcheckpoint⟩ :=
  XRr_CandidateCuts.source D pub physical proof split hash obs saved run
 have init := XRr_Initial64.init initial hinit
 have pendingInit := XRu_NewLength.source initial.weights.deref pending0 hpending
 change pending0.raw.val.length=initial.weights.val.length ∧ pending0.terms=0#usize at pendingInit
 exact ⟨p,g,initial,geo,pending0,a,pending,hinit,hpending,pendingInit.1.trans init.1,pendingInit.2,hquery⟩
#print axioms source
end XRu_CandidatePending64
