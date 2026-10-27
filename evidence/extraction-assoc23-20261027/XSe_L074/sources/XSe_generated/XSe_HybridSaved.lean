import XSe_FinishCanonical
import XSe_PrepareCuts
import XSe_PreparedRho
import XSe_PrepareVariant
import XSe_QueryPower
import XSc_QueryDestination
import XSc_FinishRestore
import XRz_HybridCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_HybridSaved
/-- The SAME real saved-cut variant/rho/power/weights/next domain components.
Other saved fields, query bounds and reached model equality remain separate. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (saved : alloc.vec.Vec U8)
 (run : XRz_HybridTx1.tx1 XRz_HybridSampler.adopted D pub physical proof split hash obs=ok (.Ok saved)) :
 ∃ (p : verifier.Prepared) (a : verifier.Accumulator),
 p.variant=.S2 ∧ XRp_PowersQAdd.CanonicalQ p.rho ∧ XRp_PowersQAdd.CanonicalQ a.power ∧
 a.weights.val.length=64 ∧ a.next.val=10 ∧
 (∀ j, (h : j < a.weights.val.length) → XRp_PowersQAdd.CanonicalQ (a.weights.val[j]'h)) ∧
 verifier.checkpoint D p a proof physical hash=ok saved := by
 obtain ⟨splitEq,shape,zero,p,g,initial,root,geo,pending0,a,pending,slice,restore,finished,
  _,_,_,hprepare,hinit,_,_,hnew,hquery,hborrow,hfinish,hcheckpoint⟩ :=
  XRz_HybridCuts.source XRz_HybridSampler.adopted D pub physical proof split hash obs saved run
 obtain ⟨semantic,y1,v,sem,hview,hprepared⟩ :=
  XSe_PrepareCuts.source XRz_HybridSampler.adopted D pub proof hash obs _ g p hprepare
 have rho := XSe_PreparedRho.source XRz_HybridSampler.adopted D sem v hash _ g p hprepared
 have variant := XSe_PrepareVariant.source XRz_HybridSampler.adopted D pub proof hash obs _ g p hprepare
 have path := XSc_QueryPath.source proof p g obs geo split (.Ok (initial,pending0)) (.Ok (a,pending)) hquery
 have power := XSe_QueryPower.reached proof p g obs geo split initial pending0 rho
  (XSe_InitialPower.source initial hinit) (.Ok (a,pending)) path
 have domain := XSc_QueryDestination.source proof p g obs geo split initial a pending0 pending slice restore
  hinit hnew hquery hborrow
 have lengths : slice.length≤pending.raw.length := by change slice.val.length≤pending.raw.val.length;omega
 obtain ⟨out,hout,hlen,canonical⟩ := XSe_FinishCanonical.source pending slice lengths
 have same := Result.ok.inj (hout.symm.trans hfinish)
 subst out
 have frame := XSc_FinishRestore.source a pending slice finished restore hborrow lengths hfinish
 refine ⟨p,{a with weights:=restore finished},variant,rho,power,?_,?_,?_,hcheckpoint⟩
 · change (restore finished).val.length=64
   rw [frame.1,frame.2,domain.1]
 · change a.next.val=10
   rw [domain.2.2,splitEq]
   unfold compact.SPLIT
   rfl
 · intro j hj
   change XRp_PowersQAdd.CanonicalQ ((restore finished).val[j]'hj)
   simpa only [frame.1] using canonical j (by simpa only [frame.1] using hj)
#print axioms source
end XSe_HybridSaved
