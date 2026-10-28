import JFr_TX2_CircleTotal
import NDO_JFn_AlphaCanonical
import FIp_CircleQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_CircleArray
open Aeneas Aeneas.Std Result SAQ_WideABI

theorem source (alpha : E) (v : Array E 4#usize) (inverse : Array U32 5#usize)
    (hAlpha : Port4C_QueryArithmetic.CanonE alpha)
    (canonical : ∀ j : Fin 4,
      Port4C_QueryArithmetic.CanonE (v.val[j.val]'(by rw [v.property];exact j.isLt))) :
    ∃ out, FIp_CircleQuery.circle alpha v inverse=ok out ∧ Port4C_QueryArithmetic.CanonE out := by
  obtain ⟨a,b,c,d,hv⟩ := SAQ_LineArrays.four v
  obtain ⟨ix,iy,lx,ly,lz,hi⟩ := SAQ_LineArrays.five inverse
  subst v
  subst inverse
  have ca := (w_canonical a).mp (canonical ⟨0,by decide⟩)
  have cb := (w_canonical b).mp (canonical ⟨1,by decide⟩)
  have cc := (w_canonical c).mp (canonical ⟨2,by decide⟩)
  have cd := (w_canonical d).mp (canonical ⟨3,by decide⟩)
  obtain ⟨out,run,canon⟩ := JFr_TX2_CircleTotal.source (toW alpha) (toW a) (toW b) (toW c) (toW d)
    ix iy lx ly lz ((w_canonical alpha).mp hAlpha) ca cb cc cd
  refine ⟨fromW out,?_,(w_canonical (fromW out)).mpr canon⟩
  change (do let z ← FIp_CircleSource.circle (toW alpha)
               (Array.make 4#usize [toW a,toW b,toW c,toW d])
               (Array.make 5#usize [ix,iy,lx,ly,lz])
             ok (fromW z))=ok (fromW out)
  rw [run,bind_tc_ok]

theorem alpha0 : Port4C_QueryArithmetic.CanonE JFq_Alpha0.scalar := by
  change (492967452<2147483647 ∧ 709301790<2147483647 ∧ 1617612614<2147483647 ∧ 599334322<2147483647) ∧
    (1668486716<2147483647 ∧ 1253062525<2147483647 ∧ 341779229<2147483647 ∧ 880523595<2147483647)
  omega

#print axioms source
#print axioms alpha0
end AspisR1.JFr_TX2_CircleArray
end
