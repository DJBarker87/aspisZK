import XSe_PrepareCuts
import XSe_PrepareVariant
import XSe_PreparedRho
import XSe_QueryPower
import XSc_HybridMaterialized
import XSc_FinishRestore
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_HybridCanonical
/-- Derived provenance at EVERY successful prefix of the SAME actual hybrid
run. This is power/variant provenance, not the full saved-field/model join. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : XRz_HybridTx1.tx1 XRz_HybridSampler.adopted D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (initial a : verifier.Accumulator) (geo : verifier.QueryGeometry)
 (pending0 pending : verifier.BatchedWeights),
 p.variant=.S2 ∧ XRp_PowersQAdd.CanonicalQ p.rho ∧
 verifier.Accumulator.new .S2=ok (.Ok initial) ∧
 verifier.BatchedWeights.new initial.weights.deref=ok (.Ok pending0) ∧
 verifier.candidate.query_loop proof p initial g obs geo pending0 split=ok (.Ok (a,pending)) ∧
 ∀ (a : verifier.Accumulator) (pending : verifier.BatchedWeights),
 XSc_QueryPath.Reached proof p g obs geo split (.Ok (initial,pending0)) (.Ok (a,pending)) →
 XRp_PowersQAdd.CanonicalQ a.power := by
 obtain ⟨_,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
  _,_,_,hprepare,hinit,_,_,hnew,hquery,_,_,_⟩ :=
  XRz_HybridCuts.source XRz_HybridSampler.adopted D pub physical proof split hash obs saved run
 obtain ⟨semantic,y1,v,sem,hview,hprepared⟩ :=
  XSe_PrepareCuts.source XRz_HybridSampler.adopted D pub proof hash obs _ g p hprepare
 have rho := XSe_PreparedRho.source XRz_HybridSampler.adopted D sem v hash _ g p hprepared
 have variant := XSe_PrepareVariant.source XRz_HybridSampler.adopted D pub proof hash obs _ g p hprepare
 refine ⟨p,g,initial,a,geo,pending0,pending,variant,rho,hinit,hnew,hquery,?_⟩
 intro a pending path
 exact XSe_QueryPower.reached proof p g obs geo split initial pending0 rho
  (XSe_InitialPower.source initial hinit) (.Ok (a,pending)) path
#print axioms source
end XSe_HybridCanonical
