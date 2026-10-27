import XSc_QueryDestination
import XRz_HybridCuts
import XRz_FinishCarrier
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_HybridMaterialized
/-- Apply whole finish transport at the SAME hybrid-run cuts, deriving its
length premise rather than assuming a separately chosen materialization domain. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : XRz_HybridTx1.tx1 XRz_HybridSampler.adopted D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (initial a : verifier.Accumulator) (geo : verifier.QueryGeometry)
 (pending0 pending : verifier.BatchedWeights) (slice finished : Slice aspis_core.field.QM31)
 (restore : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31),
 verifier.Accumulator.new .S2=ok (.Ok initial) ∧
 verifier.BatchedWeights.new initial.weights.deref=ok (.Ok pending0) ∧
 verifier.candidate.query_loop proof p initial g obs geo pending0 split=ok (.Ok (a,pending)) ∧
 lift (alloc.vec.Vec.deref_mut a.weights)=ok (slice,restore) ∧
 slice.val.length=64 ∧ pending.raw.val.length=64 ∧ a.next.val=split.val ∧
 verifier.BatchedWeights.finish pending slice=ok finished ∧
 verifier.BatchedWeights.finish pending slice=
  XRo_Join_Carriers.mapR XRz_FinishCarrier.emitted
   (S8OwnedP6.finish_owned pending.raw (XRz_FinishOwned.weights slice)) ∧
 verifier.checkpoint D p {a with weights:=restore finished} proof physical hash=ok saved := by
 obtain ⟨_,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
  _,_,_,_,hinit,_,_,hnew,hquery,hborrow,hfinish,hcheckpoint⟩ :=
  XRz_HybridCuts.source XRz_HybridSampler.adopted D pub physical proof split hash obs saved run
 have domain := XSc_QueryDestination.source proof p g obs geo split initial a pending0 pending slice restore
  hinit hnew hquery hborrow
 refine ⟨p,g,initial,a,geo,pending0,pending,slice,finished,restore,hinit,hnew,hquery,hborrow,
  domain.1,domain.2.1,domain.2.2,hfinish,?_,hcheckpoint⟩
 apply XRz_FinishCarrier.source
 change slice.val.length≤pending.raw.val.length
 omega
#print axioms source
end XSc_HybridMaterialized
